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
.build_mode: FORCE
	@echo "$(_BMODE)" > .build_mode.tmp
	@if [ ! -f .build_mode ] || ! cmp -s .build_mode.tmp .build_mode; then \
	  echo "apps.src: build mode changed to $(_BMODE), rebuilding..."; \
	  /bin/rm -f *.o; \
	  mv .build_mode.tmp .build_mode; \
	else \
	  rm -f .build_mode.tmp; \
	fi

FORCE:

PROGRAMS = latfilter olfilter clausefilter idfilter renamer unfast clausetester rewriter isofilter0 isofilter isofilter2 dprofiles interpfilter upper-covers miniscope interpformat prooftrans mirror-flip perm3 sigtest directproof test_clause_eval test_complex complex gen_trc_defs

all: ladr apps install realclean

ladr:
	cd ../ladr && $(MAKE) libladr.a

clean:
	/bin/rm -f *.o .build_mode

realclean:
	/bin/rm -f *.o $(PROGRAMS) .build_mode

install:
	@for f in $(PROGRAMS); do \
	  codesign -s - -f "$$f" 2>/dev/null || true; \
	  /bin/mv "$$f" ../bin; \
	done

tags:
	etags *.c ../ladr/*.c

apps: $(PROGRAMS)

test: test.o
	$(CC) $(CFLAGS) -o test test.o ../ladr/libladr.a

interpformat: interpformat.o
	$(CC) $(CFLAGS) -o interpformat interpformat.o ../ladr/libladr.a

prooftrans: prooftrans.o
	$(CC) $(CFLAGS) -o prooftrans prooftrans.o ../ladr/libladr.a

directproof: directproof.o
	$(CC) $(CFLAGS) -o directproof directproof.o ../ladr/libladr.a

test_clause_eval: test_clause_eval.o
	$(CC) $(CFLAGS) -o test_clause_eval test_clause_eval.o ../ladr/libladr.a

test_complex: test_complex.o
	$(CC) $(CFLAGS) -o test_complex test_complex.o ../ladr/libladr.a

complex: complex.o
	$(CC) $(CFLAGS) -o complex complex.o ../ladr/libladr.a

latfilter: latfilter.o
	$(CC) $(CFLAGS) -o latfilter latfilter.o ../ladr/libladr.a

olfilter: olfilter.o
	$(CC) $(CFLAGS) -o olfilter olfilter.o ../ladr/libladr.a

unfast: unfast.o
	$(CC) $(CFLAGS) -o unfast unfast.o ../ladr/libladr.a

upper-covers: upper-covers.o
	$(CC) $(CFLAGS) -o upper-covers upper-covers.o ../ladr/libladr.a

miniscope: miniscope.o
	$(CC) $(CFLAGS) -o miniscope miniscope.o ../ladr/libladr.a

isofilter0: isofilter0.o
	$(CC) $(CFLAGS) -o isofilter0 isofilter0.o ../ladr/libladr.a

isofilter: isofilter.o
	$(CC) $(CFLAGS) -o isofilter isofilter.o ../ladr/libladr.a

isofilter2: isofilter2.o
	$(CC) $(CFLAGS) -o isofilter2 isofilter2.o ../ladr/libladr.a

dprofiles: dprofiles.o
	$(CC) $(CFLAGS) -o dprofiles dprofiles.o ../ladr/libladr.a

renamer: renamer.o
	$(CC) $(CFLAGS) -o renamer renamer.o ../ladr/libladr.a

rewriter: rewriter.o
	$(CC) $(CFLAGS) -o rewriter rewriter.o ../ladr/libladr.a

idfilter: idfilter.o
	$(CC) $(CFLAGS) -o idfilter idfilter.o ../ladr/libladr.a

clausefilter: clausefilter.o
	$(CC) $(CFLAGS) -o clausefilter clausefilter.o ../ladr/libladr.a

interpfilter: interpfilter.o
	$(CC) $(CFLAGS) -o interpfilter interpfilter.o ../ladr/libladr.a

clausetester: clausetester.o
	$(CC) $(CFLAGS) -o clausetester clausetester.o ../ladr/libladr.a

mirror-flip: mirror-flip.o
	$(CC) $(CFLAGS) -o mirror-flip mirror-flip.o ../ladr/libladr.a

perm3: perm3.o
	$(CC) $(CFLAGS) -o perm3 perm3.o ../ladr/libladr.a

sigtest: sigtest.o
	$(CC) $(CFLAGS) -o sigtest sigtest.o ../ladr/libladr.a

rewriter2: rewriter2.o
	$(CC) $(CFLAGS) -o rewriter2 rewriter2.o ../ladr/libladr.a

gen_trc_defs: gen_trc_defs.o
	$(CC) $(CFLAGS) -o gen_trc_defs gen_trc_defs.o ../ladr/libladr.a






