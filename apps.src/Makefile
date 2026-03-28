# LADR/apps.src

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
MMD_TEST := $(shell rm -f /tmp/_mmd_test.o /tmp/_mmd_test.d; echo 'int x;' | $(CC) $(PLATFORM_FLAGS) -MMD -MP -x c -c - -o /tmp/_mmd_test.o 2>/dev/null && echo "-MMD -MP"; rm -f /tmp/_mmd_test.o /tmp/_mmd_test.d)
CFLAGS = $(OPTFLAGS) -Wall $(MMD_TEST) $(PLATFORM_FLAGS) $(XFLAGS)
ifdef STATIC
  ifneq ($(UNAME_S),Darwin)
    LDFLAGS = -static
  endif
endif

# Build mode sentinel -- auto-clean when switching debug/release.
.build_mode: FORCE
	@echo "$(_BMODE) $(XFLAGS)" > .build_mode.tmp
	@if [ ! -f .build_mode ] || ! cmp -s .build_mode.tmp .build_mode; then \
	  echo "apps.src: build mode changed to $(_BMODE), rebuilding..."; \
	  /bin/rm -f *.o; \
	  mv .build_mode.tmp .build_mode; \
	else \
	  rm -f .build_mode.tmp; \
	fi

FORCE:

PROGRAMS = latfilter olfilter clausefilter idfilter renamer unfast clausetester rewriter isofilter0 isofilter isofilter2 dprofiles interpfilter upper-covers miniscope interpformat prooftrans mirror-flip perm3 sigtest directproof test_clause_eval test_complex complex gen_trc_defs

all: ladr apps install

ladr:
	cd ../ladr && $(MAKE) libladr.a

clean:
	/bin/rm -f *.o *.d

realclean:
	/bin/rm -f *.o *.d $(PROGRAMS) .build_mode

install:
	@for f in $(PROGRAMS); do \
	  codesign -s - -f "$$f" 2>/dev/null || true; \
	  /bin/cp -p "$$f" ../bin; \
	done

tags:
	etags *.c ../ladr/*.c

LADR_LIB = ../ladr/libladr.a

apps: $(PROGRAMS)

test: test.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o test test.o $(LADR_LIB)

interpformat: interpformat.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o interpformat interpformat.o $(LADR_LIB)

prooftrans: prooftrans.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o prooftrans prooftrans.o $(LADR_LIB)

directproof: directproof.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o directproof directproof.o $(LADR_LIB)

test_clause_eval: test_clause_eval.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o test_clause_eval test_clause_eval.o $(LADR_LIB)

test_complex: test_complex.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o test_complex test_complex.o $(LADR_LIB)

complex: complex.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o complex complex.o $(LADR_LIB)

latfilter: latfilter.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o latfilter latfilter.o $(LADR_LIB)

olfilter: olfilter.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o olfilter olfilter.o $(LADR_LIB)

unfast: unfast.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o unfast unfast.o $(LADR_LIB)

upper-covers: upper-covers.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o upper-covers upper-covers.o $(LADR_LIB)

miniscope: miniscope.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o miniscope miniscope.o $(LADR_LIB)

isofilter0: isofilter0.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o isofilter0 isofilter0.o $(LADR_LIB)

isofilter: isofilter.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o isofilter isofilter.o $(LADR_LIB)

isofilter2: isofilter2.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o isofilter2 isofilter2.o $(LADR_LIB)

dprofiles: dprofiles.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o dprofiles dprofiles.o $(LADR_LIB)

renamer: renamer.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o renamer renamer.o $(LADR_LIB)

rewriter: rewriter.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o rewriter rewriter.o $(LADR_LIB)

idfilter: idfilter.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o idfilter idfilter.o $(LADR_LIB)

clausefilter: clausefilter.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o clausefilter clausefilter.o $(LADR_LIB)

interpfilter: interpfilter.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o interpfilter interpfilter.o $(LADR_LIB)

clausetester: clausetester.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o clausetester clausetester.o $(LADR_LIB)

mirror-flip: mirror-flip.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o mirror-flip mirror-flip.o $(LADR_LIB)

perm3: perm3.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o perm3 perm3.o $(LADR_LIB)

sigtest: sigtest.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o sigtest sigtest.o $(LADR_LIB)

rewriter2: rewriter2.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o rewriter2 rewriter2.o $(LADR_LIB)

gen_trc_defs: gen_trc_defs.o $(LADR_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o gen_trc_defs gen_trc_defs.o $(LADR_LIB)

DEPS := $(wildcard *.d)
ifneq ($(DEPS),)
-include $(DEPS)
endif


