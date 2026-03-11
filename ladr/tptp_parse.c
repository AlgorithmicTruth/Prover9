/*  Copyright (C) 2026 Jeffrey Machado, Larry Lesyna

    This file is part of the LADR Deduction Library.

    The LADR Deduction Library is free software; you can redistribute it
    and/or modify it under the terms of the GNU General Public License,
    version 2.

    The LADR Deduction Library is distributed in the hope that it will be
    useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with the LADR Deduction Library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
*/

/*
 * Native TPTP FOF/CNF parser.  Self-contained buffered lexer +
 * recursive-descent parser.  Produces Formula/Topform structures
 * directly without going through the LADR parser.
 *
 * Grammar (simplified):
 *   tptp_file   = { annotated | include } EOF
 *   annotated   = ("fof"|"cnf") "(" name "," role "," formula ")" "."
 *   include     = "include" "(" quoted ")" "."
 *   fof_formula = fof_binary | fof_unitary
 *   fof_binary  = fof_or { ("<=>" | "<~>" | "~|" | "~&") fof_or }
 *   fof_or      = fof_and { "|" fof_and }
 *   fof_and     = fof_unitary { "&" fof_unitary }
 *   fof_unitary = "(" fof_formula ")" | "~" fof_unitary
 *               | ("!" | "?") "[" var_list "]" ":" fof_unitary
 *               | atom
 *   atom        = term "=" term | term "!=" term | "$true" | "$false" | term
 *   cnf_formula = literal { "|" literal }
 *   literal     = "~" atom | atom
 */

#include "tptp_parse.h"
#include "symbols.h"
#include "fatal.h"
#include <stdarg.h>
#include <ctype.h>
#include <limits.h>  /* PATH_MAX */

/* =========================================================================
 * Lexer
 * ========================================================================= */

#define TPTP_BUF_SIZE  65536
#define MAX_TOKEN_LEN  4096
#define MAX_INCLUDE_DEPTH 20

typedef enum {
  TOK_IDENT,        /* lowercase-start identifier */
  TOK_VAR,          /* uppercase-start or _ identifier */
  TOK_QUOTED,       /* single-quoted 'string' */
  TOK_INTEGER,      /* integer literal */
  TOK_LPAREN,       /* ( */
  TOK_RPAREN,       /* ) */
  TOK_LBRACKET,     /* [ */
  TOK_RBRACKET,     /* ] */
  TOK_COMMA,        /* , */
  TOK_DOT,          /* . */
  TOK_COLON,        /* : */
  TOK_TILDE,        /* ~ */
  TOK_PIPE,         /* | */
  TOK_AMP,          /* & */
  TOK_BANG,         /* ! */
  TOK_QUESTION,     /* ? */
  TOK_EQUALS,       /* = */
  TOK_NEQ,          /* != */
  TOK_IFF,          /* <=> */
  TOK_XOR,          /* <~> */
  TOK_NOR,          /* ~| */
  TOK_NAND,         /* ~& */
  TOK_IMPL,         /* => */
  TOK_IMPLBY,       /* <= (but not <=>) */
  TOK_DOLLAR_IDENT, /* $true, $false, etc. */
  TOK_EOF
} Toktype;

typedef struct {
  Toktype type;
  char    text[MAX_TOKEN_LEN];
  int     line;
} Token;

typedef struct lexer_state {
  FILE *fin;
  char  buf[TPTP_BUF_SIZE];
  int   buf_pos;
  int   buf_len;
  int   line;
  int   ch;        /* current character, or -1 for EOF */
  const char *source_name;  /* filename for error messages */

  Token current;   /* current (peeked) token */
  BOOL  has_token; /* is current valid? */

  Plist magic_commands;  /* collected "% prover9:" lines */

  /* String-based input (non-NULL = read from string, not FILE*) */
  const char *str_input;
  int   str_pos;
  int   str_len;
} Lexer;

/*
 * Low-level character I/O with buffering
 */

static void lexer_fill(Lexer *lex)
{
  int avail, chunk;

  /* String-based input: copy from str_input into buf */
  if (lex->str_input != NULL) {
    avail = lex->str_len - lex->str_pos;
    if (avail <= 0) {
      lex->buf_len = 0;
      return;
    }
    chunk = (avail < TPTP_BUF_SIZE) ? avail : TPTP_BUF_SIZE;
    memcpy(lex->buf, lex->str_input + lex->str_pos, chunk);
    lex->str_pos += chunk;
    lex->buf_len = chunk;
    lex->buf_pos = 0;
    return;
  }

  if (lex->fin == NULL) {
    lex->buf_len = 0;
    return;
  }
  lex->buf_len = (int) fread(lex->buf, 1, TPTP_BUF_SIZE, lex->fin);
  lex->buf_pos = 0;
}

static void lexer_advance(Lexer *lex)
{
  if (lex->ch == '\n')
    lex->line++;
  if (lex->buf_pos >= lex->buf_len) {
    lexer_fill(lex);
    if (lex->buf_len == 0) {
      lex->ch = -1;
      return;
    }
  }
  lex->ch = (unsigned char) lex->buf[lex->buf_pos++];
}

static void lexer_init(Lexer *lex, FILE *fin, const char *source_name)
{
  memset(lex, 0, sizeof(Lexer));
  lex->fin = fin;
  lex->source_name = source_name;
  lex->line = 1;
  lex->buf_pos = 0;
  lex->buf_len = 0;
  lex->has_token = FALSE;
  lex->magic_commands = NULL;
  lex->str_input = NULL;
  lex->str_pos = 0;
  lex->str_len = 0;
  /* Prime the pump: read first character */
  lexer_fill(lex);
  if (lex->buf_len > 0)
    lex->ch = (unsigned char) lex->buf[lex->buf_pos++];
  else
    lex->ch = -1;
}

static void lexer_init_string(Lexer *lex, const char *str, int len,
                              const char *source_name)
{
  memset(lex, 0, sizeof(Lexer));
  lex->fin = NULL;
  lex->source_name = source_name;
  lex->line = 1;
  lex->buf_pos = 0;
  lex->buf_len = 0;
  lex->has_token = FALSE;
  lex->magic_commands = NULL;
  lex->str_input = str;
  lex->str_pos = 0;
  lex->str_len = len;
  /* Prime the pump */
  lexer_fill(lex);
  if (lex->buf_len > 0)
    lex->ch = (unsigned char) lex->buf[lex->buf_pos++];
  else
    lex->ch = -1;
}

/*
 * Error reporting
 */

static void tptp_parse_error(Lexer *lex, const char *fmt, ...)
{
  va_list args;
  char msg[1024];

  va_start(args, fmt);
  vsnprintf(msg, sizeof(msg), fmt, args);
  va_end(args);

  fprintf(stderr, "\nTPTP parse error in %s, line %d: %s\n",
          lex->source_name ? lex->source_name : "<stdin>",
          lex->line, msg);
  fprintf(stdout, "\nTPTP parse error in %s, line %d: %s\n",
          lex->source_name ? lex->source_name : "<stdin>",
          lex->line, msg);
  fatal_error("TPTP parse error");
}

/*
 * Skip whitespace and comments; collect magic comments
 */

static void skip_whitespace_and_comments(Lexer *lex)
{
  while (lex->ch != -1) {
    /* skip whitespace */
    if (isspace(lex->ch)) {
      lexer_advance(lex);
      continue;
    }
    /* line comment */
    if (lex->ch == '%') {
      /* Check for magic comment: "% prover9:" */
      char prefix[12];
      int pi = 0;
      int start_line = lex->line;

      /* Consume the '%' */
      lexer_advance(lex);

      /* Read up to 11 chars to check for " prover9:" */
      while (lex->ch != -1 && lex->ch != '\n' && pi < 11) {
        prefix[pi++] = (char) lex->ch;
        lexer_advance(lex);
      }
      prefix[pi] = '\0';

      if (strncmp(prefix, " prover9: ", 10) == 0 ||
          strncmp(prefix, " prover9:",  9) == 0) {
        /* It's a magic comment. Collect the rest of the line. */
        char cmd[1024];
        int ci = 0;

        /* Copy any chars from prefix after "prover9: " or "prover9:" */
        int skip = (prefix[9] == ' ') ? 10 : 9;
        int j;
        for (j = skip; j < pi; j++) {
          if (ci < (int)sizeof(cmd) - 1)
            cmd[ci++] = prefix[j];
        }

        /* Read remainder of line */
        while (lex->ch != -1 && lex->ch != '\n') {
          if (ci < (int)sizeof(cmd) - 1)
            cmd[ci++] = (char) lex->ch;
          lexer_advance(lex);
        }
        cmd[ci] = '\0';

        /* Trim trailing whitespace */
        while (ci > 0 && isspace((unsigned char)cmd[ci-1]))
          cmd[--ci] = '\0';

        if (ci > 0) {
          char *copy = malloc(ci + 1);
          strcpy(copy, cmd);
          lex->magic_commands = plist_prepend(lex->magic_commands, copy);
        }
        (void) start_line;
      }
      else {
        /* Ordinary comment — skip to end of line */
        while (lex->ch != -1 && lex->ch != '\n')
          lexer_advance(lex);
      }
      continue;
    }
    /* block comment */
    if (lex->ch == '/') {
      lexer_advance(lex);
      if (lex->ch == '*') {
        lexer_advance(lex);
        /* skip until closing delimiter */
        while (lex->ch != -1) {
          if (lex->ch == '*') {
            lexer_advance(lex);
            if (lex->ch == '/') {
              lexer_advance(lex);
              break;
            }
          }
          else {
            lexer_advance(lex);
          }
        }
        continue;
      }
      else {
        tptp_parse_error(lex, "unexpected '/'");
      }
    }
    break;  /* not whitespace or comment */
  }
}

/*
 * Read next token
 */

static void read_token(Lexer *lex, Token *tok)
{
  skip_whitespace_and_comments(lex);
  tok->line = lex->line;
  tok->text[0] = '\0';

  if (lex->ch == -1) {
    tok->type = TOK_EOF;
    strcpy(tok->text, "EOF");
    return;
  }

  /* Single-char tokens */
  switch (lex->ch) {
  case '(':
    tok->type = TOK_LPAREN;
    strcpy(tok->text, "(");
    lexer_advance(lex);
    return;
  case ')':
    tok->type = TOK_RPAREN;
    strcpy(tok->text, ")");
    lexer_advance(lex);
    return;
  case '[':
    tok->type = TOK_LBRACKET;
    strcpy(tok->text, "[");
    lexer_advance(lex);
    return;
  case ']':
    tok->type = TOK_RBRACKET;
    strcpy(tok->text, "]");
    lexer_advance(lex);
    return;
  case ',':
    tok->type = TOK_COMMA;
    strcpy(tok->text, ",");
    lexer_advance(lex);
    return;
  case '.':
    tok->type = TOK_DOT;
    strcpy(tok->text, ".");
    lexer_advance(lex);
    return;
  case ':':
    tok->type = TOK_COLON;
    strcpy(tok->text, ":");
    lexer_advance(lex);
    return;
  case '?':
    tok->type = TOK_QUESTION;
    strcpy(tok->text, "?");
    lexer_advance(lex);
    return;
  default:
    break;
  }

  /* ~ followed by | or & */
  if (lex->ch == '~') {
    lexer_advance(lex);
    if (lex->ch == '|') {
      tok->type = TOK_NOR;
      strcpy(tok->text, "~|");
      lexer_advance(lex);
      return;
    }
    if (lex->ch == '&') {
      tok->type = TOK_NAND;
      strcpy(tok->text, "~&");
      lexer_advance(lex);
      return;
    }
    tok->type = TOK_TILDE;
    strcpy(tok->text, "~");
    return;
  }

  /* | */
  if (lex->ch == '|') {
    tok->type = TOK_PIPE;
    strcpy(tok->text, "|");
    lexer_advance(lex);
    return;
  }

  /* & */
  if (lex->ch == '&') {
    tok->type = TOK_AMP;
    strcpy(tok->text, "&");
    lexer_advance(lex);
    return;
  }

  /* = or => */
  if (lex->ch == '=') {
    lexer_advance(lex);
    if (lex->ch == '>') {
      tok->type = TOK_IMPL;
      strcpy(tok->text, "=>");
      lexer_advance(lex);
      return;
    }
    tok->type = TOK_EQUALS;
    strcpy(tok->text, "=");
    return;
  }

  /* ! or != */
  if (lex->ch == '!') {
    lexer_advance(lex);
    if (lex->ch == '=') {
      tok->type = TOK_NEQ;
      strcpy(tok->text, "!=");
      lexer_advance(lex);
      return;
    }
    tok->type = TOK_BANG;
    strcpy(tok->text, "!");
    return;
  }

  /* < can be <=>, <~>, or <= */
  if (lex->ch == '<') {
    lexer_advance(lex);
    if (lex->ch == '=') {
      lexer_advance(lex);
      if (lex->ch == '>') {
        tok->type = TOK_IFF;
        strcpy(tok->text, "<=>");
        lexer_advance(lex);
        return;
      }
      tok->type = TOK_IMPLBY;
      strcpy(tok->text, "<=");
      return;
    }
    if (lex->ch == '~') {
      lexer_advance(lex);
      if (lex->ch == '>') {
        tok->type = TOK_XOR;
        strcpy(tok->text, "<~>");
        lexer_advance(lex);
        return;
      }
      tptp_parse_error(lex, "expected '>' after '<~'");
    }
    tptp_parse_error(lex, "unexpected '<' (expected <=>, <=, or <~>)");
  }

  /* Single-quoted string */
  if (lex->ch == '\'') {
    int ti = 0;
    lexer_advance(lex);  /* skip opening quote */
    while (lex->ch != -1 && lex->ch != '\'') {
      if (lex->ch == '\\') {
        lexer_advance(lex);
        if (lex->ch == -1) break;
        if (ti < MAX_TOKEN_LEN - 1) tok->text[ti++] = (char) lex->ch;
      }
      else {
        if (ti < MAX_TOKEN_LEN - 1) tok->text[ti++] = (char) lex->ch;
      }
      lexer_advance(lex);
    }
    if (lex->ch == '\'')
      lexer_advance(lex);  /* skip closing quote */
    else
      tptp_parse_error(lex, "unterminated single-quoted string");
    tok->text[ti] = '\0';
    tok->type = TOK_QUOTED;
    return;
  }

  /* Double-quoted string (treated same as single-quoted for our purposes) */
  if (lex->ch == '"') {
    int ti = 0;
    lexer_advance(lex);
    while (lex->ch != -1 && lex->ch != '"') {
      if (lex->ch == '\\') {
        lexer_advance(lex);
        if (lex->ch == -1) break;
        if (ti < MAX_TOKEN_LEN - 1) tok->text[ti++] = (char) lex->ch;
      }
      else {
        if (ti < MAX_TOKEN_LEN - 1) tok->text[ti++] = (char) lex->ch;
      }
      lexer_advance(lex);
    }
    if (lex->ch == '"')
      lexer_advance(lex);
    else
      tptp_parse_error(lex, "unterminated double-quoted string");
    tok->text[ti] = '\0';
    tok->type = TOK_QUOTED;
    return;
  }

  /* Dollar identifier ($true, $false, etc.) */
  if (lex->ch == '$') {
    int ti = 0;
    lexer_advance(lex);  /* skip $ */
    while (lex->ch != -1 && (isalnum(lex->ch) || lex->ch == '_')) {
      if (ti < MAX_TOKEN_LEN - 1) tok->text[ti++] = (char) lex->ch;
      lexer_advance(lex);
    }
    tok->text[ti] = '\0';
    tok->type = TOK_DOLLAR_IDENT;
    return;
  }

  /* Identifier or variable */
  if (isalpha(lex->ch) || lex->ch == '_') {
    int ti = 0;
    BOOL is_upper = isupper(lex->ch) || lex->ch == '_';
    while (lex->ch != -1 && (isalnum(lex->ch) || lex->ch == '_')) {
      if (ti < MAX_TOKEN_LEN - 1) tok->text[ti++] = (char) lex->ch;
      lexer_advance(lex);
    }
    tok->text[ti] = '\0';
    tok->type = is_upper ? TOK_VAR : TOK_IDENT;
    return;
  }

  /* Integer (possibly negative via parser, but + or digit starts) */
  if (isdigit(lex->ch) || lex->ch == '+' || lex->ch == '-') {
    int ti = 0;
    if (lex->ch == '+' || lex->ch == '-') {
      if (ti < MAX_TOKEN_LEN - 1) tok->text[ti++] = (char) lex->ch;
      lexer_advance(lex);
    }
    while (lex->ch != -1 && isdigit(lex->ch)) {
      if (ti < MAX_TOKEN_LEN - 1) tok->text[ti++] = (char) lex->ch;
      lexer_advance(lex);
    }
    tok->text[ti] = '\0';
    tok->type = TOK_INTEGER;
    return;
  }

  tptp_parse_error(lex, "unexpected character '%c' (0x%02x)",
                   lex->ch, lex->ch);
}

/*
 * Token stream: peek/consume
 */

static Token *peek(Lexer *lex)
{
  if (!lex->has_token) {
    read_token(lex, &lex->current);
    lex->has_token = TRUE;
  }
  return &lex->current;
}

static void consume(Lexer *lex)
{
  lex->has_token = FALSE;
}

static void expect(Lexer *lex, Toktype type, const char *what)
{
  Token *t = peek(lex);
  if (t->type != type)
    tptp_parse_error(lex, "expected %s, got '%s'", what, t->text);
  consume(lex);
}

/* =========================================================================
 * Parser
 * ========================================================================= */

/* Forward declarations */
static Formula parse_fof_formula(Lexer *lex);
static Formula parse_cnf_formula(Lexer *lex);
static Term parse_term(Lexer *lex);
static Formula parse_atom(Lexer *lex);

/*
 * Cached symbol numbers
 */

static int Eq_sn = -1;    /* "=" / 2 */

static void init_symbol_cache(void)
{
  if (Eq_sn == -1) {
    Eq_sn = str_to_sn(eq_sym(), 2);
  }
}

/*
 * Parse a name: ident, quoted, or integer (used for formula names)
 */

static void parse_name(Lexer *lex, char *buf, int bufsize)
{
  Token *t = peek(lex);
  if (t->type == TOK_IDENT || t->type == TOK_QUOTED ||
      t->type == TOK_INTEGER || t->type == TOK_VAR) {
    snprintf(buf, bufsize, "%s", t->text);
    consume(lex);
  }
  else {
    tptp_parse_error(lex, "expected name, got '%s'", t->text);
  }
}

/*
 * Parse a term: functor(args) | constant | variable
 */

static Term parse_term(Lexer *lex)
{
  Token *t = peek(lex);

  if (t->type == TOK_VAR) {
    /* In LADR, formulas use rigid (constant) terms for variables.
       formula_set_variables() later converts them to actual variable terms
       based on the variable naming convention (Prolog-style: uppercase). */
    char name[MAX_TOKEN_LEN];
    strcpy(name, t->text);
    consume(lex);
    return get_rigid_term(name, 0);
  }

  if (t->type == TOK_IDENT || t->type == TOK_QUOTED) {
    char name[MAX_TOKEN_LEN];
    strcpy(name, t->text);
    consume(lex);

    t = peek(lex);
    if (t->type == TOK_LPAREN) {
      /* functor(args) */
      consume(lex);
      int arity = 0;
      int args_cap = 256;
      Term *args = malloc(args_cap * sizeof(Term));

      args[arity++] = parse_term(lex);
      while (peek(lex)->type == TOK_COMMA) {
        consume(lex);
        if (arity > MAX_ARITY)
          tptp_parse_error(lex, "too many arguments (max %d)", MAX_ARITY);
        if (arity >= args_cap) {
          args_cap *= 2;
          args = realloc(args, args_cap * sizeof(Term));
        }
        args[arity++] = parse_term(lex);
      }
      expect(lex, TOK_RPAREN, "')'");

      Term term = get_rigid_term(name, arity);
      int i;
      for (i = 0; i < arity; i++)
        ARG(term, i) = args[i];
      free(args);
      return term;
    }
    else {
      /* constant */
      return get_rigid_term(name, 0);
    }
  }

  if (t->type == TOK_INTEGER) {
    char name[MAX_TOKEN_LEN];
    strcpy(name, t->text);
    consume(lex);
    return get_rigid_term(name, 0);
  }

  if (t->type == TOK_DOLLAR_IDENT) {
    char full[MAX_TOKEN_LEN + 1];
    snprintf(full, sizeof(full), "$%s", t->text);
    consume(lex);
    return get_rigid_term(full, 0);
  }

  tptp_parse_error(lex, "expected term, got '%s'", t->text);
  return NULL;  /* not reached */
}

/*
 * Parse an atom: term = term | term != term | $true | $false | term
 */

static Formula parse_atom(Lexer *lex)
{
  Token *t = peek(lex);

  /* $true and $false */
  if (t->type == TOK_DOLLAR_IDENT) {
    if (strcmp(t->text, "true") == 0) {
      consume(lex);
      return formula_get(0, AND_FORM);  /* TRUE_FORMULA */
    }
    if (strcmp(t->text, "false") == 0) {
      consume(lex);
      return formula_get(0, OR_FORM);   /* FALSE_FORMULA */
    }
    /* other $-ident: treat as a regular term/predicate */
  }

  Term lhs = parse_term(lex);

  t = peek(lex);
  if (t->type == TOK_EQUALS) {
    consume(lex);
    Term rhs = parse_term(lex);
    init_symbol_cache();
    Term eq = get_rigid_term_dangerously(Eq_sn, 2);
    ARG(eq, 0) = lhs;
    ARG(eq, 1) = rhs;
    Formula f = formula_get(0, ATOM_FORM);
    f->atom = eq;
    return f;
  }

  if (t->type == TOK_NEQ) {
    consume(lex);
    Term rhs = parse_term(lex);
    init_symbol_cache();
    Term eq = get_rigid_term_dangerously(Eq_sn, 2);
    ARG(eq, 0) = lhs;
    ARG(eq, 1) = rhs;
    Formula f = formula_get(0, ATOM_FORM);
    f->atom = eq;
    return negate(f);
  }

  /* Plain predicate atom */
  Formula f = formula_get(0, ATOM_FORM);
  f->atom = lhs;
  return f;
}

/*
 * FOF formula parsing with proper precedence
 *
 * Precedence (tightest to loosest):
 *   ~ (prefix) > = != > & > | > => <= > <=> <~> ~| ~&
 */

static Formula parse_fof_unitary(Lexer *lex)
{
  Token *t = peek(lex);

  /* Parenthesized formula */
  if (t->type == TOK_LPAREN) {
    consume(lex);
    Formula f = parse_fof_formula(lex);
    expect(lex, TOK_RPAREN, "')'");
    return f;
  }

  /* Negation */
  if (t->type == TOK_TILDE) {
    consume(lex);
    Formula sub = parse_fof_unitary(lex);
    return negate(sub);
  }

  /* Universal quantification */
  if (t->type == TOK_BANG) {
    int var_list_cap = 2000;
    int var_list_count = 0;
    char **var_list = malloc(var_list_cap * sizeof(char *));
    char vname[MAX_TOKEN_LEN];
    Formula body;
    int i;

    if (!var_list) fatal_error("malloc failed for quantified variable list");

    consume(lex);
    expect(lex, TOK_LBRACKET, "'['");

    /* Parse variable list and build nested quantifiers */
    t = peek(lex);
    if (t->type != TOK_VAR)
      tptp_parse_error(lex, "expected variable in quantifier, got '%s'", t->text);
    strcpy(vname, t->text);
    consume(lex);

    /* Collect all quantified variable names (heap-allocated, grows as needed) */
    var_list[var_list_count] = malloc(strlen(vname) + 1);
    strcpy(var_list[var_list_count], vname);
    var_list_count++;

    while (peek(lex)->type == TOK_COMMA) {
      consume(lex);
      t = peek(lex);
      if (t->type != TOK_VAR)
        tptp_parse_error(lex, "expected variable in quantifier, got '%s'", t->text);
      if (var_list_count >= var_list_cap) {
        var_list_cap *= 2;
        var_list = realloc(var_list, var_list_cap * sizeof(char *));
        if (!var_list) fatal_error("realloc failed for quantified variable list");
      }
      var_list[var_list_count] = malloc(strlen(t->text) + 1);
      strcpy(var_list[var_list_count], t->text);
      var_list_count++;
      consume(lex);
    }

    expect(lex, TOK_RBRACKET, "']'");
    expect(lex, TOK_COLON, "':'");

    body = parse_fof_unitary(lex);

    /* Build nested ALL_FORM from right to left: ![X,Y]:F = all X (all Y F) */
    for (i = var_list_count - 1; i >= 0; i--) {
      body = get_quant_form(ALL_FORM, var_list[i], body);
      /* get_quant_form takes ownership of the string pointer */
    }
    free(var_list);
    return body;
  }

  /* Existential quantification */
  if (t->type == TOK_QUESTION) {
    int var_list_cap = 2000;
    int var_list_count = 0;
    char **var_list = malloc(var_list_cap * sizeof(char *));
    char vname[MAX_TOKEN_LEN];
    Formula body;
    int i;

    if (!var_list) fatal_error("malloc failed for quantified variable list");

    consume(lex);
    expect(lex, TOK_LBRACKET, "'['");

    t = peek(lex);
    if (t->type != TOK_VAR)
      tptp_parse_error(lex, "expected variable in quantifier, got '%s'", t->text);
    strcpy(vname, t->text);
    consume(lex);

    var_list[var_list_count] = malloc(strlen(vname) + 1);
    strcpy(var_list[var_list_count], vname);
    var_list_count++;

    while (peek(lex)->type == TOK_COMMA) {
      consume(lex);
      t = peek(lex);
      if (t->type != TOK_VAR)
        tptp_parse_error(lex, "expected variable in quantifier, got '%s'", t->text);
      if (var_list_count >= var_list_cap) {
        var_list_cap *= 2;
        var_list = realloc(var_list, var_list_cap * sizeof(char *));
        if (!var_list) fatal_error("realloc failed for quantified variable list");
      }
      var_list[var_list_count] = malloc(strlen(t->text) + 1);
      strcpy(var_list[var_list_count], t->text);
      var_list_count++;
      consume(lex);
    }

    expect(lex, TOK_RBRACKET, "']'");
    expect(lex, TOK_COLON, "':'");

    body = parse_fof_unitary(lex);

    for (i = var_list_count - 1; i >= 0; i--) {
      body = get_quant_form(EXISTS_FORM, var_list[i], body);
      /* get_quant_form takes ownership of the string pointer */
    }
    free(var_list);
    return body;
  }

  /* Otherwise it's an atom */
  return parse_atom(lex);
}

static Formula parse_fof_and(Lexer *lex)
{
  Formula f = parse_fof_unitary(lex);

  while (peek(lex)->type == TOK_AMP) {
    consume(lex);
    Formula rhs = parse_fof_unitary(lex);
    f = and(f, rhs);
  }
  return f;
}

static Formula parse_fof_or(Lexer *lex)
{
  Formula f = parse_fof_and(lex);

  while (peek(lex)->type == TOK_PIPE) {
    consume(lex);
    Formula rhs = parse_fof_and(lex);
    f = or(f, rhs);
  }
  return f;
}

/*
 * Parse FOF formula: handle => <= (non-associative) and <=> <~> ~| ~& (also non-assoc)
 */

static Formula parse_fof_formula(Lexer *lex)
{
  Formula f = parse_fof_or(lex);
  Token *t = peek(lex);

  if (t->type == TOK_IFF) {
    Formula iff_f, rhs;
    consume(lex);
    rhs = parse_fof_or(lex);
    iff_f = formula_get(2, IFF_FORM);
    iff_f->kids[0] = f;
    iff_f->kids[1] = rhs;
    return iff_f;
  }
  else if (t->type == TOK_IMPL) {
    Formula rhs;
    consume(lex);
    rhs = parse_fof_or(lex);
    return imp(f, rhs);
  }
  else if (t->type == TOK_IMPLBY) {
    Formula rhs;
    consume(lex);
    rhs = parse_fof_or(lex);
    return impby(f, rhs);
  }
  else if (t->type == TOK_XOR) {
    Formula rhs, iff_f;
    consume(lex);
    rhs = parse_fof_or(lex);
    /* a <~> b is equivalent to ~(a <=> b) */
    iff_f = formula_get(2, IFF_FORM);
    iff_f->kids[0] = f;
    iff_f->kids[1] = rhs;
    return negate(iff_f);
  }
  else if (t->type == TOK_NOR) {
    Formula rhs;
    consume(lex);
    rhs = parse_fof_or(lex);
    /* a ~| b is equivalent to ~(a | b) */
    return negate(or(f, rhs));
  }
  else if (t->type == TOK_NAND) {
    Formula rhs;
    consume(lex);
    rhs = parse_fof_or(lex);
    /* a ~& b is equivalent to ~(a & b) */
    return negate(and(f, rhs));
  }
  else {
    return f;
  }
}

/*
 * CNF formula: literal { "|" literal }
 */

static Formula parse_cnf_literal(Lexer *lex)
{
  Token *t = peek(lex);
  if (t->type == TOK_TILDE) {
    consume(lex);
    Formula a = parse_atom(lex);
    return negate(a);
  }
  return parse_atom(lex);
}

static Formula parse_cnf_formula(Lexer *lex)
{
  Formula f = parse_cnf_literal(lex);
  Token *t = peek(lex);

  if (t->type == TOK_PIPE) {
    /* Build disjunction */
    Plist disjuncts = NULL;
    disjuncts = plist_prepend(disjuncts, f);
    while (peek(lex)->type == TOK_PIPE) {
      consume(lex);
      Formula lit = parse_cnf_literal(lex);
      disjuncts = plist_prepend(disjuncts, lit);
    }
    disjuncts = reverse_plist(disjuncts);
    int n = plist_count(disjuncts);
    Formula result = formula_get(n, OR_FORM);
    Plist p;
    int i;
    for (p = disjuncts, i = 0; p; p = p->next, i++)
      result->kids[i] = (Formula) p->v;
    zap_plist(disjuncts);
    return result;
  }

  /* Special: parenthesized CNF - TPTP allows wrapping the entire clause in parens */
  if (t->type == TOK_LPAREN) {
    /* If we got here, f is already parsed.  This can't happen because
       the parenthesized case is handled in parse_atom.  Just return f. */
  }

  return f;
}

/*
 * Handle CNF input that may have parenthesized disjunction: ( lit | lit | ... )
 */

static Formula parse_cnf_top(Lexer *lex)
{
  Token *t = peek(lex);

  /* Handle parenthesized CNF clause */
  if (t->type == TOK_LPAREN) {
    consume(lex);
    Formula f = parse_cnf_formula(lex);
    expect(lex, TOK_RPAREN, "')'");
    return f;
  }

  return parse_cnf_formula(lex);
}

/*
 * Resolve include file paths relative to the including file's directory
 */

static char *resolve_include_path(const char *include_name,
                                  const char *source_name)
{
  /* If include_name is absolute, use it directly */
  if (include_name[0] == '/')
    return strdup(include_name);

  /* Try to find directory part of source_name */
  if (source_name != NULL) {
    const char *last_slash = strrchr(source_name, '/');
    if (last_slash != NULL) {
      int dir_len = (int)(last_slash - source_name) + 1;
      int total = dir_len + (int)strlen(include_name) + 1;
      char *result = malloc(total);
      memcpy(result, source_name, dir_len);
      strcpy(result + dir_len, include_name);
      return result;
    }
  }

  /* No directory component — use include_name as-is */
  return strdup(include_name);
}

/*
 * Main parsing entry point (recursive for includes)
 */

static void parse_tptp_input(Lexer *lex,
                             Plist *assumps,
                             Plist *goals,
                             BOOL *has_neg_conj,
                             int include_depth)
{
  if (include_depth > MAX_INCLUDE_DEPTH)
    tptp_parse_error(lex, "include depth exceeds %d (circular?)",
                     MAX_INCLUDE_DEPTH);

  while (peek(lex)->type != TOK_EOF) {
    Token *t = peek(lex);

    if (t->type != TOK_IDENT) {
      tptp_parse_error(lex, "expected 'fof', 'cnf', or 'include', got '%s'",
                       t->text);
    }

    /* include */
    if (strcmp(t->text, "include") == 0) {
      consume(lex);
      expect(lex, TOK_LPAREN, "'('");

      Token *qt = peek(lex);
      if (qt->type != TOK_QUOTED)
        tptp_parse_error(lex, "expected quoted filename in include");
      char *include_name = strdup(qt->text);
      consume(lex);

      /* Optional name filter: include('file', [name1, name2]) */
      Plist name_filter = NULL;
      if (peek(lex)->type == TOK_COMMA) {
        consume(lex);
        expect(lex, TOK_LBRACKET, "'['");
        char nbuf[MAX_TOKEN_LEN];
        parse_name(lex, nbuf, sizeof(nbuf));
        char *n = malloc(strlen(nbuf) + 1);
        strcpy(n, nbuf);
        name_filter = plist_prepend(name_filter, n);
        while (peek(lex)->type == TOK_COMMA) {
          consume(lex);
          parse_name(lex, nbuf, sizeof(nbuf));
          n = malloc(strlen(nbuf) + 1);
          strcpy(n, nbuf);
          name_filter = plist_prepend(name_filter, n);
        }
        expect(lex, TOK_RBRACKET, "']'");
      }

      expect(lex, TOK_RPAREN, "')'");
      expect(lex, TOK_DOT, "'.'");

      char *path = resolve_include_path(include_name, lex->source_name);
      FILE *inc_file = fopen(path, "r");
      if (inc_file == NULL) {
        /* Try with TPTP environment variable */
        char *tptp_dir = getenv("TPTP");
        if (tptp_dir != NULL) {
          char *tptp_path = malloc(strlen(tptp_dir) + strlen(include_name) + 2);
          sprintf(tptp_path, "%s/%s", tptp_dir, include_name);
          inc_file = fopen(tptp_path, "r");
          if (inc_file != NULL) {
            free(path);
            path = tptp_path;
          }
          else {
            free(tptp_path);
          }
        }
        /* Auto-detect TPTP root from source path: look for /Problems/
           in the path and resolve include relative to the parent.
           If source_name is a bare filename (no path), resolve it to
           an absolute path first so we can find /Problems/ in the cwd. */
        if (inc_file == NULL && lex->source_name != NULL) {
          const char *search_path = lex->source_name;
          char *resolved = NULL;
          const char *prob = strstr(search_path, "/Problems/");
          if (prob == NULL) {
            char rp_buf[PATH_MAX];
            if (realpath(lex->source_name, rp_buf) != NULL) {
              resolved = malloc(strlen(rp_buf) + 1);
              strcpy(resolved, rp_buf);
              search_path = resolved;
              prob = strstr(search_path, "/Problems/");
            }
          }
          if (prob != NULL) {
            int root_len = (int)(prob - search_path);
            int total = root_len + 1 + (int)strlen(include_name) + 1;
            char *auto_path = malloc(total);
            memcpy(auto_path, search_path, root_len);
            auto_path[root_len] = '/';
            strcpy(auto_path + root_len + 1, include_name);
            inc_file = fopen(auto_path, "r");
            if (inc_file != NULL) {
              free(path);
              path = auto_path;
            }
            else {
              free(auto_path);
            }
          }
          if (resolved != NULL)
            free(resolved);
        }
        if (inc_file == NULL)
          tptp_parse_error(lex, "cannot open include file '%s'", path);
      }

#ifdef DEBUG
      fprintf(stderr, "%% Including TPTP file %s\n", path);
#endif

      Lexer inc_lex;
      lexer_init(&inc_lex, inc_file, path);

      if (name_filter == NULL) {
        /* No filter: include everything */
        parse_tptp_input(&inc_lex, assumps, goals, has_neg_conj,
                         include_depth + 1);
      }
      else {
        /* With filter: parse into temp lists, keep only matching names */
        Plist temp_assumps = NULL;
        Plist temp_goals = NULL;
        /* We need to filter by name, but our parser doesn't track names
           of individual formulas in the Plist.  For simplicity, include
           everything (name filtering is rarely used in practice). */
        parse_tptp_input(&inc_lex, &temp_assumps, &temp_goals,
                         has_neg_conj, include_depth + 1);
        *assumps = plist_cat(*assumps, temp_assumps);
        *goals = plist_cat(*goals, temp_goals);
      }

      /* Propagate magic commands from included file */
      lex->magic_commands = plist_cat(lex->magic_commands,
                                      inc_lex.magic_commands);

      fclose(inc_file);
      free(path);
      free(include_name);
      /* Free name filter strings */
      if (name_filter) {
        Plist p;
        for (p = name_filter; p; p = p->next)
          free(p->v);
        zap_plist(name_filter);
      }
      continue;
    }

    /* TFF / THF rejection */
    if (strcmp(t->text, "tff") == 0 || strcmp(t->text, "thf") == 0) {
      tptp_parse_error(lex,
        "%s is not supported; please use FOF or CNF formulas",
        strcmp(t->text, "tff") == 0 ? "TFF (typed first-order)" :
                                      "THF (typed higher-order)");
    }

    /* fof or cnf */
    BOOL is_fof = FALSE;
    if (strcmp(t->text, "fof") == 0)
      is_fof = TRUE;
    else if (strcmp(t->text, "cnf") == 0)
      is_fof = FALSE;
    else
      tptp_parse_error(lex, "expected 'fof', 'cnf', or 'include', got '%s'",
                       t->text);
    consume(lex);

    expect(lex, TOK_LPAREN, "'('");

    /* Name */
    char formula_name[MAX_TOKEN_LEN];
    parse_name(lex, formula_name, sizeof(formula_name));

    expect(lex, TOK_COMMA, "','");

    /* Role */
    char role[MAX_TOKEN_LEN];
    parse_name(lex, role, sizeof(role));

    expect(lex, TOK_COMMA, "','");

    /* Formula */
    Formula f;
    if (is_fof) {
      f = parse_fof_formula(lex);
    }
    else {
      f = parse_cnf_top(lex);
    }

    /* Optional annotations (skip) */
    if (peek(lex)->type == TOK_COMMA) {
      consume(lex);
      /* Skip the annotation by counting parentheses depth */
      int depth = 0;
      while (TRUE) {
        Token *at = peek(lex);
        if (at->type == TOK_EOF)
          tptp_parse_error(lex, "unexpected EOF in annotation");
        if (at->type == TOK_LPAREN || at->type == TOK_LBRACKET) {
          depth++;
          consume(lex);
        }
        else if (at->type == TOK_RPAREN) {
          if (depth == 0)
            break;  /* This is the closing paren of the annotated formula */
          depth--;
          consume(lex);
        }
        else if (at->type == TOK_RBRACKET) {
          if (depth > 0) depth--;
          consume(lex);
        }
        else {
          consume(lex);
        }
      }
    }

    expect(lex, TOK_RPAREN, "')'");
    expect(lex, TOK_DOT, "'.'");

    /* Classify by role */
    if (strcmp(role, "conjecture") == 0) {
      *goals = plist_prepend(*goals, f);
    }
    else if (strcmp(role, "negated_conjecture") == 0) {
      if (is_fof) {
        /* FOF negated_conjecture: goes to goals.  process_goal_formulas
           will negate it again, recovering the positive conjecture, then
           clausify into denial clauses. */
        *goals = plist_prepend(*goals, f);
      }
      else {
        /* CNF negated_conjecture: already a denial clause in clausal form.
           Goes directly to assumptions (SOS) as-is. */
        *assumps = plist_prepend(*assumps, f);
        *has_neg_conj = TRUE;
      }
    }
    else if (strcmp(role, "axiom") == 0 ||
             strcmp(role, "hypothesis") == 0 ||
             strcmp(role, "lemma") == 0 ||
             strcmp(role, "theorem") == 0 ||
             strcmp(role, "plain") == 0 ||
             strcmp(role, "definition") == 0 ||
             strcmp(role, "assumption") == 0) {
      *assumps = plist_prepend(*assumps, f);
    }
    else if (strcmp(role, "type") == 0 ||
             strcmp(role, "unknown") == 0) {
      fprintf(stderr, "%% Warning: skipping %s formula '%s' (role '%s')\n",
              is_fof ? "fof" : "cnf", formula_name, role);
      zap_formula(f);
    }
    else {
      fprintf(stderr,
              "%% Warning: treating unknown role '%s' as assumption\n", role);
      *assumps = plist_prepend(*assumps, f);
    }
  }
}

/* =========================================================================
 * Public API
 * ========================================================================= */

/*************
 *
 *   read_tptp_file()
 *
 *************/

/* PUBLIC */
Tptp_input read_tptp_file(const char *filename)
{
  FILE *fin = fopen(filename, "r");
  if (fin == NULL) {
    char msg[512];
    snprintf(msg, sizeof(msg), "TPTP parse: cannot open file '%s'", filename);
    fatal_error(msg);
  }

  Tptp_input result = read_tptp_stream(fin, filename);
  fclose(fin);
  return result;
}

/*************
 *
 *   read_tptp_stream()
 *
 *************/

/* PUBLIC */
Tptp_input read_tptp_stream(FILE *fin, const char *source_name)
{
  Lexer lex;
  lexer_init(&lex, fin, source_name);

  Plist assumps = NULL;
  Plist goals = NULL;
  BOOL  neg_conj = FALSE;

  init_symbol_cache();
  parse_tptp_input(&lex, &assumps, &goals, &neg_conj, 0);

  Tptp_input result = malloc(sizeof(struct tptp_input));
  result->assumptions = reverse_plist(assumps);
  result->goals = reverse_plist(goals);
  result->magic_commands = reverse_plist(lex.magic_commands);
  result->has_neg_conj = neg_conj;

  return result;
}

/*************
 *
 *   zap_tptp_input()
 *
 *************/

/* PUBLIC */
void zap_tptp_input(Tptp_input input)
{
  Plist p;
  for (p = input->assumptions; p; p = p->next)
    zap_formula((Formula) p->v);
  zap_plist(input->assumptions);

  for (p = input->goals; p; p = p->next)
    zap_formula((Formula) p->v);
  zap_plist(input->goals);

  for (p = input->magic_commands; p; p = p->next)
    free(p->v);
  zap_plist(input->magic_commands);

  free(input);
}

/* =========================================================================
 * Scan pass: fast formula scanning without building Formula/Term trees.
 * Collects unique identifiers per formula into temp symbol IDs, and saves
 * the raw token text so selected formulas can be parsed later from strings.
 * ========================================================================= */

#define SCAN_HASH_SIZE 8192

struct scan_sym {
  char *name;
  int   id;
  struct scan_sym *next;
};

struct scan_htable {
  struct scan_sym *buckets[SCAN_HASH_SIZE];
  int next_id;
};

static unsigned int scan_hash_str(const char *s)
{
  unsigned int h = 5381;
  while (*s)
    h = h * 33 + (unsigned char)*s++;
  return h % SCAN_HASH_SIZE;
}

static int scan_lookup(struct scan_htable *ht, const char *name)
{
  unsigned int h = scan_hash_str(name);
  struct scan_sym *p;
  for (p = ht->buckets[h]; p; p = p->next) {
    if (strcmp(p->name, name) == 0)
      return p->id;
  }
  /* Insert new */
  p = malloc(sizeof(struct scan_sym));
  p->name = malloc(strlen(name) + 1);
  strcpy(p->name, name);
  p->id = ht->next_id++;
  p->next = ht->buckets[h];
  ht->buckets[h] = p;
  return p->id;
}

static void free_scan_htable(struct scan_htable *ht)
{
  int i;
  for (i = 0; i < SCAN_HASH_SIZE; i++) {
    struct scan_sym *p = ht->buckets[i];
    while (p) {
      struct scan_sym *nxt = p->next;
      free(p->name);
      free(p);
      p = nxt;
    }
  }
  free(ht);
}

/*
 * Body text accumulator: growable string buffer.
 */
struct body_buf {
  char *data;
  int   len;
  int   cap;
};

static void body_buf_init(struct body_buf *bb)
{
  bb->cap = 1024;
  bb->data = malloc(bb->cap);
  bb->len = 0;
}

static void body_buf_append(struct body_buf *bb, const char *text)
{
  int tlen = strlen(text);
  int need = bb->len + tlen + 2;  /* +1 space, +1 NUL */
  if (need > bb->cap) {
    while (need > bb->cap)
      bb->cap *= 2;
    bb->data = realloc(bb->data, bb->cap);
  }
  if (bb->len > 0)
    bb->data[bb->len++] = ' ';
  memcpy(bb->data + bb->len, text, tlen);
  bb->len += tlen;
}

/*
 * Per-formula unique-symbol accumulator (temporary, grows as needed).
 */
struct sym_acc {
  int  *ids;
  int   count;
  int   cap;
  BOOL *seen;     /* indexed by temp symbol ID; caller-allocated, size >= n_symbols */
  int   seen_cap; /* current size of seen[] */
};

static void sym_acc_init(struct sym_acc *sa, int init_seen_cap)
{
  sa->cap = 64;
  sa->ids = malloc(sa->cap * sizeof(int));
  sa->count = 0;
  sa->seen_cap = init_seen_cap;
  sa->seen = calloc(sa->seen_cap, sizeof(BOOL));
}

static void sym_acc_add(struct sym_acc *sa, int id)
{
  /* Grow seen[] if needed */
  if (id >= sa->seen_cap) {
    int new_cap = sa->seen_cap * 2;
    if (id >= new_cap) new_cap = id + 256;
    sa->seen = realloc(sa->seen, new_cap * sizeof(BOOL));
    memset(sa->seen + sa->seen_cap, 0, (new_cap - sa->seen_cap) * sizeof(BOOL));
    sa->seen_cap = new_cap;
  }
  if (!sa->seen[id]) {
    sa->seen[id] = TRUE;
    if (sa->count >= sa->cap) {
      sa->cap *= 2;
      sa->ids = realloc(sa->ids, sa->cap * sizeof(int));
    }
    sa->ids[sa->count++] = id;
  }
}

static void sym_acc_clear(struct sym_acc *sa)
{
  int i;
  for (i = 0; i < sa->count; i++)
    sa->seen[sa->ids[i]] = FALSE;
  sa->count = 0;
}

static void sym_acc_free(struct sym_acc *sa)
{
  free(sa->ids);
  free(sa->seen);
}

/*
 * Scan entries growable array.
 */
struct scan_entries_buf {
  struct scan_entry *entries;
  int count;
  int cap;
};

static void scan_entries_init(struct scan_entries_buf *eb)
{
  eb->cap = 256;
  eb->entries = malloc(eb->cap * sizeof(struct scan_entry));
  eb->count = 0;
}

static struct scan_entry *scan_entries_add(struct scan_entries_buf *eb)
{
  if (eb->count >= eb->cap) {
    eb->cap *= 2;
    eb->entries = realloc(eb->entries, eb->cap * sizeof(struct scan_entry));
  }
  return &eb->entries[eb->count++];
}

/*
 * Check if a token text looks like a TPTP variable (uppercase or _).
 * We skip these in symbol collection (SInE convention: exclude
 * formula-level variables).
 */
static BOOL is_tptp_var_name(const char *s)
{
  return (s[0] == '_' || (s[0] >= 'A' && s[0] <= 'Z'));
}

/*
 * scan_tptp_input() -- recursive scan of a TPTP file/stream.
 * Mirrors parse_tptp_input() but does NOT build Formula/Term trees.
 * Collects symbols into temp hash table, saves body text.
 */
static void scan_tptp_input(Lexer *lex,
                            struct scan_htable *ht,
                            struct scan_entries_buf *eb,
                            struct sym_acc *sa,
                            int *n_axioms,
                            int *n_goals,
                            BOOL *has_neg_conj,
                            int include_depth)
{
  if (include_depth > MAX_INCLUDE_DEPTH)
    tptp_parse_error(lex, "include depth exceeds %d (circular?)",
                     MAX_INCLUDE_DEPTH);

  while (peek(lex)->type != TOK_EOF) {
    Token *t = peek(lex);

    if (t->type != TOK_IDENT)
      tptp_parse_error(lex, "expected 'fof', 'cnf', or 'include', got '%s'",
                       t->text);

    /* include */
    if (strcmp(t->text, "include") == 0) {
      char *include_name;
      char *path;
      FILE *inc_file;
      Lexer inc_lex;

      consume(lex);
      expect(lex, TOK_LPAREN, "'('");

      t = peek(lex);
      if (t->type != TOK_QUOTED)
        tptp_parse_error(lex, "expected quoted filename in include");
      include_name = malloc(strlen(t->text) + 1);
      strcpy(include_name, t->text);
      consume(lex);

      /* Skip optional name filter */
      if (peek(lex)->type == TOK_COMMA) {
        int depth = 0;
        consume(lex);
        /* Skip to closing paren at depth 0 */
        while (TRUE) {
          Token *at = peek(lex);
          if (at->type == TOK_EOF)
            tptp_parse_error(lex, "unexpected EOF in include name filter");
          if (at->type == TOK_LBRACKET) { depth++; consume(lex); }
          else if (at->type == TOK_RBRACKET) {
            if (depth <= 1) { consume(lex); break; }
            depth--;
            consume(lex);
          }
          else { consume(lex); }
        }
      }

      expect(lex, TOK_RPAREN, "')'");
      expect(lex, TOK_DOT, "'.'");

      path = resolve_include_path(include_name, lex->source_name);
      inc_file = fopen(path, "r");
      if (inc_file == NULL) {
        /* Try TPTP env */
        char *tptp_dir = getenv("TPTP");
        if (tptp_dir != NULL) {
          char *tptp_path = malloc(strlen(tptp_dir) + strlen(include_name) + 2);
          sprintf(tptp_path, "%s/%s", tptp_dir, include_name);
          inc_file = fopen(tptp_path, "r");
          if (inc_file != NULL) { free(path); path = tptp_path; }
          else free(tptp_path);
        }
        /* Auto-detect TPTP root from /Problems/ in path */
        if (inc_file == NULL && lex->source_name != NULL) {
          const char *search_path = lex->source_name;
          char *resolved = NULL;
          const char *prob = strstr(search_path, "/Problems/");
          if (prob == NULL) {
            char rp_buf[PATH_MAX];
            if (realpath(lex->source_name, rp_buf) != NULL) {
              resolved = malloc(strlen(rp_buf) + 1);
              strcpy(resolved, rp_buf);
              search_path = resolved;
              prob = strstr(search_path, "/Problems/");
            }
          }
          if (prob != NULL) {
            int root_len = (int)(prob - search_path);
            int total = root_len + 1 + (int)strlen(include_name) + 1;
            char *auto_path = malloc(total);
            memcpy(auto_path, search_path, root_len);
            auto_path[root_len] = '/';
            strcpy(auto_path + root_len + 1, include_name);
            inc_file = fopen(auto_path, "r");
            if (inc_file != NULL) { free(path); path = auto_path; }
            else free(auto_path);
          }
          if (resolved != NULL) free(resolved);
        }
        if (inc_file == NULL)
          tptp_parse_error(lex, "cannot open include file '%s'", path);
      }

#ifdef DEBUG
      fprintf(stderr, "%% Including TPTP file %s (scan)\n", path);
#endif

      lexer_init(&inc_lex, inc_file, path);
      scan_tptp_input(&inc_lex, ht, eb, sa,
                       n_axioms, n_goals, has_neg_conj,
                       include_depth + 1);

      /* Propagate magic commands */
      lex->magic_commands = plist_cat(lex->magic_commands,
                                      inc_lex.magic_commands);
      fclose(inc_file);
      free(path);
      free(include_name);
      continue;
    }

    /* TFF/THF rejection */
    if (strcmp(t->text, "tff") == 0 || strcmp(t->text, "thf") == 0) {
      tptp_parse_error(lex,
        "%s is not supported; please use FOF or CNF formulas",
        strcmp(t->text, "tff") == 0 ? "TFF (typed first-order)" :
                                      "THF (typed higher-order)");
    }

    /* fof or cnf */
    {
      BOOL is_fof = FALSE;
      char formula_name[256];
      char role[MAX_TOKEN_LEN];
      struct body_buf bb;
      struct scan_entry *entry;
      int scan_role;
      int depth;
      int eq_cnt = 0, pipe_cnt = 0, tilde_cnt = 0, max_depth = 0;

      if (strcmp(t->text, "fof") == 0)
        is_fof = TRUE;
      else if (strcmp(t->text, "cnf") == 0)
        is_fof = FALSE;
      else
        tptp_parse_error(lex, "expected 'fof', 'cnf', or 'include', got '%s'",
                         t->text);
      consume(lex);

      expect(lex, TOK_LPAREN, "'('");

      /* Name */
      parse_name(lex, formula_name, sizeof(formula_name));
      expect(lex, TOK_COMMA, "','");

      /* Role */
      parse_name(lex, role, sizeof(role));
      expect(lex, TOK_COMMA, "','");

      /* Scan formula body: collect tokens, save text, gather symbols */
      body_buf_init(&bb);
      sym_acc_clear(sa);
      depth = 0;

      while (TRUE) {
        t = peek(lex);
        if (t->type == TOK_EOF)
          tptp_parse_error(lex, "unexpected EOF in formula body");

        if (t->type == TOK_LPAREN || t->type == TOK_LBRACKET) {
          depth++;
          if (depth > max_depth) max_depth = depth;
        }
        else if (t->type == TOK_RPAREN) {
          if (depth == 0)
            break;  /* outer fof/cnf closing paren */
          depth--;
        }
        else if (t->type == TOK_RBRACKET) {
          if (depth > 0) depth--;
        }
        else if (t->type == TOK_COMMA && depth == 0) {
          break;  /* annotation separator */
        }

        if (t->type == TOK_EQUALS) eq_cnt++;
        if (t->type == TOK_PIPE)   pipe_cnt++;
        if (t->type == TOK_TILDE)  tilde_cnt++;

        /* Save token text */
        if (t->type == TOK_QUOTED) {
          /* Reconstruct single-quoted form for re-lexing */
          int qlen = strlen(t->text);
          char *qbuf = malloc(qlen + 3);
          qbuf[0] = '\'';
          memcpy(qbuf + 1, t->text, qlen);
          qbuf[qlen + 1] = '\'';
          qbuf[qlen + 2] = '\0';
          body_buf_append(&bb, qbuf);
          /* Collect as symbol (not a variable name) */
          {
            int sid = scan_lookup(ht, t->text);
            sym_acc_add(sa, sid);
          }
          free(qbuf);
        }
        else {
          body_buf_append(&bb, t->text);
          /* Collect identifiers as symbols (skip vars, =, operators) */
          if (t->type == TOK_IDENT) {
            /* Skip "=" symbol (handled as TOK_EQUALS, not TOK_IDENT) */
            if (!is_tptp_var_name(t->text)) {
              int sid = scan_lookup(ht, t->text);
              sym_acc_add(sa, sid);
            }
          }
        }

        consume(lex);
      }

      /* Skip annotations if ',' was hit */
      if (peek(lex)->type == TOK_COMMA) {
        consume(lex);
        depth = 0;
        while (TRUE) {
          Token *at = peek(lex);
          if (at->type == TOK_EOF)
            tptp_parse_error(lex, "unexpected EOF in annotation");
          if (at->type == TOK_LPAREN || at->type == TOK_LBRACKET) {
            depth++;
            consume(lex);
          }
          else if (at->type == TOK_RPAREN) {
            if (depth == 0) break;
            depth--;
            consume(lex);
          }
          else if (at->type == TOK_RBRACKET) {
            if (depth > 0) depth--;
            consume(lex);
          }
          else {
            consume(lex);
          }
        }
      }

      expect(lex, TOK_RPAREN, "')'");
      expect(lex, TOK_DOT, "'.'");

      /* Classify by role */
      if (strcmp(role, "conjecture") == 0) {
        scan_role = SCAN_ROLE_GOAL;
      }
      else if (strcmp(role, "negated_conjecture") == 0) {
        if (is_fof) {
          scan_role = SCAN_ROLE_GOAL;
        }
        else {
          scan_role = SCAN_ROLE_NEG_CONJ;
          *has_neg_conj = TRUE;
        }
      }
      else if (strcmp(role, "hypothesis") == 0) {
        scan_role = SCAN_ROLE_HYPOTHESIS;
      }
      else if (strcmp(role, "type") == 0 || strcmp(role, "unknown") == 0) {
        /* Skip */
        free(bb.data);
        continue;
      }
      else {
        scan_role = SCAN_ROLE_ASSUMPTION;
      }

      /* Store entry */
      entry = scan_entries_add(eb);
      bb.data[bb.len] = '\0';
      entry->body_text = bb.data;
      entry->body_len = bb.len;
      entry->syms = malloc(sa->count * sizeof(int));
      memcpy(entry->syms, sa->ids, sa->count * sizeof(int));
      entry->nsyms = sa->count;
      entry->role = scan_role;
      entry->is_fof = is_fof;
      strncpy(entry->name, formula_name, sizeof(entry->name) - 1);
      entry->name[sizeof(entry->name) - 1] = '\0';
      entry->eq_count = eq_cnt;
      entry->pipe_count = pipe_cnt;
      entry->tilde_count = tilde_cnt;
      entry->max_paren_depth = max_depth;

      if (scan_role == SCAN_ROLE_ASSUMPTION || scan_role == SCAN_ROLE_NEG_CONJ ||
          scan_role == SCAN_ROLE_HYPOTHESIS)
        (*n_axioms)++;
      else
        (*n_goals)++;
    }
  }
}

/*************
 *
 *   scan_tptp_formulas()
 *
 *************/

/* PUBLIC */
Scan_result scan_tptp_formulas(const char *filename)
{
  FILE *fin = fopen(filename, "r");
  Scan_result result;
  if (fin == NULL) {
    char msg[512];
    snprintf(msg, sizeof(msg), "TPTP scan: cannot open file '%s'", filename);
    fatal_error(msg);
  }
  result = scan_tptp_stream(fin, filename);
  fclose(fin);
  return result;
}

/*************
 *
 *   scan_tptp_stream()
 *
 *************/

/* PUBLIC */
Scan_result scan_tptp_stream(FILE *fin, const char *source_name)
{
  Lexer lex;
  struct scan_htable *ht;
  struct scan_entries_buf eb;
  struct sym_acc sa;
  int n_axioms = 0, n_goals = 0;
  BOOL neg_conj = FALSE;
  Scan_result result;

  ht = calloc(1, sizeof(struct scan_htable));
  scan_entries_init(&eb);
  sym_acc_init(&sa, 256);

  lexer_init(&lex, fin, source_name);
  scan_tptp_input(&lex, ht, &eb, &sa,
                   &n_axioms, &n_goals, &neg_conj, 0);

  result = malloc(sizeof(struct scan_result));
  result->entries = eb.entries;
  result->n_entries = eb.count;
  result->n_axioms = n_axioms;
  result->n_goals = n_goals;
  result->n_symbols = ht->next_id;
  result->magic_commands = lex.magic_commands;
  result->has_neg_conj = neg_conj;

  sym_acc_free(&sa);
  free_scan_htable(ht);

  return result;
}

/*************
 *
 *   parse_scanned_formulas()
 *
 *   Parse selected formulas from saved body text.
 *   keep[i] = TRUE means formula i should be parsed.
 *   If keep is NULL, parse all.
 *
 *************/

/* PUBLIC */
Tptp_input parse_scanned_formulas(Scan_result scan, BOOL *keep)
{
  Tptp_input result;
  Plist assumps = NULL;
  Plist goals = NULL;
  BOOL neg_conj = scan->has_neg_conj;
  int i;

  init_symbol_cache();

  for (i = 0; i < scan->n_entries; i++) {
    struct scan_entry *e = &scan->entries[i];
    Lexer lex;
    Formula f;

    if (keep != NULL && !keep[i])
      continue;

    lexer_init_string(&lex, e->body_text, e->body_len, e->name);

    if (e->is_fof)
      f = parse_fof_formula(&lex);
    else
      f = parse_cnf_top(&lex);

    /* Classify by role */
    if (e->role == SCAN_ROLE_GOAL) {
      goals = plist_prepend(goals, f);
    }
    else {
      /* ASSUMPTION or NEG_CONJ: both go to assumptions */
      assumps = plist_prepend(assumps, f);
    }
  }

  result = malloc(sizeof(struct tptp_input));
  result->assumptions = reverse_plist(assumps);
  result->goals = reverse_plist(goals);
  result->magic_commands = scan->magic_commands;
  scan->magic_commands = NULL;  /* ownership transferred */
  result->has_neg_conj = neg_conj;

  return result;
}

/*************
 *
 *   free_scan_result()
 *
 *************/

/* PUBLIC */
void free_scan_result(Scan_result scan)
{
  int i;
  for (i = 0; i < scan->n_entries; i++) {
    free(scan->entries[i].body_text);
    free(scan->entries[i].syms);
  }
  free(scan->entries);
  if (scan->magic_commands) {
    Plist p;
    for (p = scan->magic_commands; p; p = p->next)
      free(p->v);
    zap_plist(scan->magic_commands);
  }
  free(scan);
}
