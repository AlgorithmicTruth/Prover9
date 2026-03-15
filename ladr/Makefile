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
else
  ifdef NATIVE
    OPTFLAGS = -O3 -march=native -flto
    PLATFORM_FLAGS =
    AR_CMD = $(AR) rs
    ifdef PGO
      ifeq ($(PGO),gen)
        OPTFLAGS += -fprofile-generate=$(CURDIR)/../pgo_data
        _BMODE = native-pgo-gen
      endif
      ifeq ($(PGO),use)
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
endif
CFLAGS = $(OPTFLAGS) -Wall -MMD -MP $(PLATFORM_FLAGS) $(XFLAGS)

# Build mode sentinel -- auto-clean when switching debug/release.
# Without this, 'make all DEBUG=1' followed by 'make all' silently
# links debug-compiled objects into the release binary.
.build_mode: FORCE
	@echo "$(_BMODE) $(XFLAGS)" > .build_mode.tmp
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
	/bin/rm -f *.o *.d

realclean:
	/bin/rm -f *.o *.d *.a .build_mode

protos:
	util/make_protos $(OBJECTS)

htmls:
	util/make_htmls $(OBJECTS)
	cp index.html.master html/index.html

tags:
	etags *.c

dio-solo:
	$(CC) $(CFLAGS) -DSOLO -o dio dioph.c

-include $(wildcard *.d)
