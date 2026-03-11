# LADR/ladr

CC = gcc

# XFLAGS can be specified on the command line (see XFLAGS below)

# Detect OS and set platform-specific flags
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    # macOS: detect Darwin version and set appropriate architectures
    # Darwin 20+ (macOS 11+): arm64 + x86_64
    # Darwin 18-19 (macOS 10.14-10.15): x86_64 only (32-bit SDK dropped)
    # Darwin 10-17 (macOS 10.6-10.13): i386 + x86_64
    # Darwin 9 (macOS 10.5): ppc + i386 + x86_64
    # Darwin 8 (macOS 10.4) Intel: ppc + i386 (no x86_64 support)
    # Darwin 8 (macOS 10.4) PPC: ppc only (cannot cross-compile i386)
    # Darwin <8 (macOS 10.3 and earlier): ppc only
    # Override: make all PLATFORM_FLAGS="-arch ppc"
    DARWIN_MAJOR := $(shell uname -r | cut -d. -f1)
    PLATFORM_FLAGS := $(shell \
        v=$(DARWIN_MAJOR); \
        if [ $$v -ge 20 ]; then \
            echo "-arch arm64 -arch x86_64"; \
        elif [ $$v -ge 18 ]; then \
            echo "-arch x86_64"; \
        elif [ $$v -ge 10 ]; then \
            echo "-arch i386 -arch x86_64"; \
        elif [ $$v -ge 9 ]; then \
            echo "-arch ppc -arch i386 -arch x86_64"; \
        elif [ $$v -ge 8 ]; then \
            p=`uname -p`; \
            if [ "$$p" = "i386" ]; then \
                echo "-arch ppc -arch i386"; \
            else \
                echo "-arch ppc"; \
            fi; \
        else \
            echo "-arch ppc"; \
        fi)
    # Use libtool for fat libraries (ar can't handle fat .o files)
    AR_CMD = libtool -static -o
else
    # Linux and others: no special flags
    PLATFORM_FLAGS =
    AR_CMD = $(AR) rs
endif

ifdef DEBUG
  OPTFLAGS = -g -O0
  _BMODE = debug
else ifdef NATIVE
  OPTFLAGS = -O3 -march=native -flto
  PLATFORM_FLAGS =
  AR_CMD = $(AR) rs
  ifdef PGO
    ifeq ($(PGO),gen)
      OPTFLAGS += -fprofile-generate=$(CURDIR)/../pgo_data
      _BMODE = native-pgo-gen
    else ifeq ($(PGO),use)
      OPTFLAGS += -fprofile-use=$(CURDIR)/../pgo_data
      _BMODE = native-pgo-use
    endif
  else
    _BMODE = native
  endif
else
  OPTFLAGS = -O2
  _BMODE = release
endif
CFLAGS = $(XFLAGS) $(OPTFLAGS) -Wall $(PLATFORM_FLAGS)

# Build mode sentinel -- auto-clean when switching debug/release.
# Without this, 'make all DEBUG=1' followed by 'make all' silently
# links debug-compiled objects into the release binary.
.build_mode: FORCE
	@echo "$(_BMODE)" > .build_mode.tmp
	@if [ ! -f .build_mode ] || ! cmp -s .build_mode.tmp .build_mode; then \
	  echo "ladr: build mode changed to $(_BMODE), rebuilding..."; \
	  /bin/rm -f *.o *.a; \
	  mv .build_mode.tmp .build_mode; \
	else \
	  rm -f .build_mode.tmp; \
	fi

FORCE:

BASE_OBJ = order.o clock.o nonport.o\
	   fatal.o ibuffer.o memory.o hash.o string.o strbuf.o\
           glist.o options.o symbols.o avltree.o
TERM_OBJ = term.o termflag.o listterm.o tlist.o flatterm.o multiset.o\
	   termorder.o parse.o accanon.o
UNIF_OBJ = unify.o fpalist.o fpa.o discrim.o discrimb.o discrimw.o\
           dioph.o btu.o btm.o mindex.o basic.o attrib.o
CLAS_OBJ = formula.o definitions.o literals.o topform.o clist.o\
	   clauseid.o clauses.o\
	   just.o cnf.o clausify.o parautil.o\
           pindex.o compress.o\
           maximal.o lindex.o weight.o weight2.o\
           int_code.o features.o di_tree.o fastparse.o\
           random.o subsume.o clause_misc.o clause_eval.o complex.o
INFE_OBJ = dollar.o flatdemod.o demod.o clash.o resolve.o paramod.o\
           backdemod.o\
           hints.o ac_redun.o xproofs.o ivy.o
MODL_OBJ = interp.o
MISC_OBJ = std_options.o banner.o ioutil.o tptp_trans.o top_input.o tptp_parse.o sine.o tstp_proof.o


OBJECTS = $(BASE_OBJ) $(TERM_OBJ) $(UNIF_OBJ) $(CLAS_OBJ)\
          $(INFE_OBJ) $(MODL_OBJ) $(MISC_OBJ)

libladr.a: .build_mode $(OBJECTS)
	$(AR_CMD) libladr.a $(OBJECTS)

##############################################################################

lib ladr libladr:
	$(MAKE) libladr.a

dep:
	util/make_dep $(OBJECTS)

clean:
	/bin/rm -f *.o .build_mode

realclean:
	/bin/rm -f *.o *.a .build_mode

protos:
	util/make_protos $(OBJECTS)

htmls:
	util/make_htmls $(OBJECTS)
	cp index.html.master html/index.html

tags:
	etags *.c

dio-solo:
	$(CC) $(CFLAGS) -DSOLO -o dio dioph.c

# The rest of the file is generated automatically by util/make_dep

order.o:   	order.h 

clock.o:   	clock.h string.h memory.h fatal.h header.h

nonport.o:   	nonport.h 

fatal.o:   	fatal.h header.h

ibuffer.o:   	ibuffer.h fatal.h header.h

memory.o:   	memory.h fatal.h header.h

hash.o:   	hash.h memory.h fatal.h header.h

string.o:   	string.h memory.h fatal.h header.h

strbuf.o:   	strbuf.h string.h memory.h fatal.h header.h

glist.o:   	glist.h order.h string.h memory.h fatal.h header.h

options.o:   	options.h string.h memory.h fatal.h header.h

symbols.o:   	symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

avltree.o:   	avltree.h memory.h order.h fatal.h header.h

term.o:   	term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

termflag.o:   	termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

listterm.o:   	listterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

tlist.o:   	tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

flatterm.o:   	flatterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

multiset.o:   	multiset.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

termorder.o:   	termorder.h flatterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

parse.o:   	parse.h listterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

accanon.o:   	accanon.h termflag.h termorder.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h flatterm.h

unify.o:   	unify.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

fpalist.o:   	fpalist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

fpa.o:   	fpa.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

discrim.o:   	discrim.h unify.h index.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

discrimb.o:   	discrimb.h discrim.h unify.h index.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

discrimw.o:   	discrimw.h discrim.h unify.h index.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

dioph.o:   	dioph.h 

btu.o:   	btu.h dioph.h unify.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

btm.o:   	btm.h unify.h accanon.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h termorder.h flatterm.h

mindex.o:   	mindex.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h

basic.o:   	basic.h unify.h termflag.h listterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

attrib.o:   	attrib.h unify.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

formula.o:   	formula.h attrib.h tlist.h termorder.h hash.h unify.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h flatterm.h

definitions.o:   	definitions.h formula.h topform.h clauseid.h just.h attrib.h tlist.h termorder.h hash.h unify.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h flatterm.h literals.h maximal.h parse.h

literals.o:   	literals.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

topform.o:   	topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

clist.o:   	clist.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

clauseid.o:   	clauseid.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

clauses.o:   	clauses.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

just.o:   	just.h clauseid.h parse.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

cnf.o:   	cnf.h formula.h clock.h attrib.h tlist.h termorder.h hash.h unify.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h flatterm.h

clausify.o:   	clausify.h topform.h cnf.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h clock.h

parautil.o:   	parautil.h 

pindex.o:   	pindex.h clist.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

compress.o:   	compress.h parautil.h

maximal.o:   	maximal.h literals.h termorder.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h flatterm.h

lindex.o:   	lindex.h mindex.h maximal.h topform.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h literals.h tlist.h attrib.h formula.h hash.h

weight.o:   	weight.h literals.h unify.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h listterm.h

weight2.o:   	weight2.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

int_code.o:   	int_code.h just.h ibuffer.h clauseid.h parse.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

features.o:   	features.h literals.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h

di_tree.o:   	di_tree.h features.h topform.h literals.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h attrib.h formula.h maximal.h unify.h listterm.h termorder.h hash.h flatterm.h

fastparse.o:   	fastparse.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

random.o:   	random.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

subsume.o:   	subsume.h parautil.h lindex.h features.h mindex.h maximal.h topform.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h literals.h tlist.h attrib.h formula.h hash.h

clause_misc.o:   	clause_misc.h clist.h mindex.h just.h basic.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h fpa.h discrimb.h discrimw.h btu.h btm.h index.h fpalist.h discrim.h dioph.h accanon.h clauseid.h parse.h

clause_eval.o:   	clause_eval.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

complex.o:   	complex.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

dollar.o:   	dollar.h clist.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h

flatdemod.o:   	flatdemod.h parautil.h mindex.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h

demod.o:   	demod.h parautil.h mindex.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h

clash.o:   	clash.h mindex.h parautil.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h

resolve.o:   	resolve.h clash.h lindex.h mindex.h parautil.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h maximal.h topform.h literals.h tlist.h attrib.h formula.h hash.h

paramod.o:   	paramod.h resolve.h basic.h clash.h lindex.h mindex.h parautil.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h maximal.h topform.h literals.h tlist.h attrib.h formula.h hash.h

backdemod.o:   	backdemod.h demod.h clist.h parautil.h mindex.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h topform.h literals.h attrib.h formula.h maximal.h tlist.h hash.h

hints.o:   	hints.h subsume.h clist.h backdemod.h resolve.h parautil.h lindex.h features.h mindex.h maximal.h topform.h fpa.h discrimb.h discrimw.h btu.h btm.h unify.h index.h fpalist.h listterm.h termflag.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h discrim.h dioph.h accanon.h termorder.h flatterm.h literals.h tlist.h attrib.h formula.h hash.h demod.h clash.h

ac_redun.o:   	ac_redun.h parautil.h accanon.h termflag.h termorder.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h flatterm.h

xproofs.o:   	xproofs.h clauses.h clause_misc.h paramod.h subsume.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h clist.h mindex.h just.h basic.h fpa.h discrimb.h discrimw.h btu.h btm.h index.h fpalist.h discrim.h dioph.h accanon.h clauseid.h parse.h resolve.h clash.h lindex.h parautil.h features.h

ivy.o:   	ivy.h xproofs.h clauses.h clause_misc.h paramod.h subsume.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h unify.h listterm.h termorder.h hash.h flatterm.h clist.h mindex.h just.h basic.h fpa.h discrimb.h discrimw.h btu.h btm.h index.h fpalist.h discrim.h dioph.h accanon.h clauseid.h parse.h resolve.h clash.h lindex.h parautil.h features.h

interp.o:   	interp.h parse.h topform.h listterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h unify.h termorder.h hash.h flatterm.h

std_options.o:   	std_options.h options.h symbols.h clock.h string.h memory.h fatal.h header.h strbuf.h glist.h order.h

banner.o:   	banner.h nonport.h clock.h string.h memory.h fatal.h header.h

ioutil.o:   	ioutil.h parse.h fastparse.h ivy.h clausify.h listterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h unify.h termorder.h hash.h flatterm.h xproofs.h clauses.h clause_misc.h paramod.h subsume.h clist.h mindex.h just.h basic.h fpa.h discrimb.h discrimw.h btu.h btm.h index.h fpalist.h discrim.h dioph.h accanon.h clauseid.h resolve.h clash.h lindex.h parautil.h features.h cnf.h clock.h

tptp_trans.o:   	tptp_trans.h ioutil.h clausify.h parse.h fastparse.h ivy.h listterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h unify.h termorder.h hash.h flatterm.h xproofs.h clauses.h clause_misc.h paramod.h subsume.h clist.h mindex.h just.h basic.h fpa.h discrimb.h discrimw.h btu.h btm.h index.h fpalist.h discrim.h dioph.h accanon.h clauseid.h resolve.h clash.h lindex.h parautil.h features.h cnf.h clock.h

top_input.o:   	top_input.h ioutil.h std_options.h tptp_trans.h parse.h fastparse.h ivy.h clausify.h listterm.h term.h symbols.h strbuf.h glist.h string.h memory.h fatal.h header.h order.h topform.h literals.h attrib.h formula.h maximal.h termflag.h tlist.h unify.h termorder.h hash.h flatterm.h xproofs.h clauses.h clause_misc.h paramod.h subsume.h clist.h mindex.h just.h basic.h fpa.h discrimb.h discrimw.h btu.h btm.h index.h fpalist.h discrim.h dioph.h accanon.h clauseid.h resolve.h clash.h lindex.h parautil.h features.h cnf.h clock.h options.h

tptp_parse.o:   	tptp_parse.h formula.h topform.h symbols.h fatal.h glist.h term.h strbuf.h string.h memory.h header.h order.h attrib.h tlist.h termorder.h hash.h unify.h listterm.h termflag.h flatterm.h literals.h maximal.h

sine.o:   	sine.h formula.h symbols.h glist.h term.h strbuf.h string.h memory.h fatal.h header.h order.h attrib.h tlist.h termorder.h hash.h unify.h listterm.h termflag.h flatterm.h

tstp_proof.o:   	tstp_proof.h topform.h ioutil.h tptp_trans.h clauseid.h just.h
