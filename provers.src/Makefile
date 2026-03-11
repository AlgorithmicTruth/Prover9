# LADR/prover9.src

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
  OPTFLAGS = -g -O0 -DDEBUG
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
	  echo "provers.src: build mode changed to $(_BMODE), rebuilding..."; \
	  /bin/rm -f *.o; \
	  mv .build_mode.tmp .build_mode; \
	else \
	  rm -f .build_mode.tmp; \
	fi

FORCE:

PRVR_OBJ = index_lits.o forward_subsume.o demodulate.o\
           pred_elim.o unfold.o semantics.o\
	   giv_select.o white_black.o actions.o\
	   search.o\
	   utilities.o\
	   provers.o\
	   foffer.o\
	   features.o dtree.o

OBJECTS = $(PRVR_OBJ)

# PROGRAMS = mprover iterate4

PROGRAMS = prover9 fof-prover9 autosketches4 newauto newsax\
	   ladr_to_tptp tptp_to_ladr

##############################################################################

all: libs $(PROGRAMS) install clean

libs: ladr libmace4

ladr libladr:
	cd ../ladr && $(MAKE) libladr
	$(MAKE) clean

libmace libmace4:
	cd ../mace4.src && $(MAKE) libmace4
	$(MAKE) clean

install:
	@for f in $(PROGRAMS); do \
	  codesign -s - -f "$$f" 2>/dev/null || true; \
	  /bin/mv "$$f" ../bin; \
	done

clean:
	/bin/rm -f *.o .build_mode

realclean:
	/bin/rm -f *.o $(PROGRAMS) .build_mode

protos:
	util/make_protos $(OBJECTS)

dep:
	util/make_dep $(OBJECTS)

tags:
	etags *.c ../ladr/*.c

prover:
	/bin/rm -f prover9
	$(MAKE) prover9

prover9: .build_mode prover9.o $(OBJECTS)
	$(CC) $(CFLAGS) -o prover9 prover9.o $(OBJECTS) ../ladr/libladr.a -lm

fof-prover9: fof-prover9.o $(OBJECTS)
	$(CC) $(CFLAGS) -o fof-prover9 fof-prover9.o $(OBJECTS) ../ladr/libladr.a -lm

ladr_to_tptp: ladr_to_tptp.o $(OBJECTS)
	$(CC) $(CFLAGS) -o ladr_to_tptp ladr_to_tptp.o $(OBJECTS) ../ladr/libladr.a -lm

tptp_to_ladr: tptp_to_ladr.o $(OBJECTS)
	$(CC) $(CFLAGS) -o tptp_to_ladr tptp_to_ladr.o $(OBJECTS) ../ladr/libladr.a -lm

autosketches4: autosketches4.o $(OBJECTS)
	$(CC) $(CFLAGS) -o autosketches4 autosketches4.o $(OBJECTS) ../ladr/libladr.a -lm

newauto: newauto.o $(OBJECTS)
	$(CC) $(CFLAGS) -o newauto newauto.o $(OBJECTS) ../ladr/libladr.a -lm

newsax: newsax.o $(OBJECTS)
	$(CC) $(CFLAGS) -o newsax newsax.o $(OBJECTS) ../ladr/libladr.a -lm

cgrep: cgrep.o $(OBJECTS)
	$(CC) $(CFLAGS) -o cgrep cgrep.o $(OBJECTS) ../ladr/libladr.a

mprover: mprover.o $(OBJECTS)
	$(CC) $(CFLAGS) -o mprover mprover.o $(OBJECTS) ../ladr/libladr.a ../mace4.src/libmace4.a

iterate4: iterate4.o $(OBJECTS)
	$(CC) $(CFLAGS) -o iterate4 iterate4.o $(OBJECTS) ../ladr/libladr.a

prover9.o mprover.o iterate4.o autosketches4.o fof-prover9.o: search.h utilities.h  forward_subsume.h giv_select.h white_black.h demodulate.h actions.h index_lits.h pred_elim.h unfold.h provers.h

# The rest of the file is generated automatically by util/make_dep

index_lits.o:   	index_lits.h ../ladr/clock.h ../ladr/subsume.h ../ladr/di_tree.h

forward_subsume.o:   	forward_subsume.h ../ladr/subsume.h ../ladr/clock.h

demodulate.o:   	demodulate.h ../ladr/ladr.h

pred_elim.o:   	pred_elim.h ../ladr/subsume.h ../ladr/resolve.h ../ladr/clauses.h ../ladr/clause_misc.h ../ladr/ioutil.h

unfold.o:   	unfold.h ../ladr/parautil.h ../ladr/clist.h ../ladr/ioutil.h

semantics.o:   	semantics.h ../ladr/interp.h ../ladr/ioutil.h

giv_select.o:   	giv_select.h search-structures.h

white_black.o:   	white_black.h search-structures.h

actions.o:   	actions.h search-structures.h

search.o:   	search.h search-structures.h semantics.h pred_elim.h demodulate.h index_lits.h forward_subsume.h unfold.h actions.h giv_select.h white_black.h utilities.h ../ladr/interp.h ../ladr/ioutil.h ../ladr/subsume.h ../ladr/resolve.h ../ladr/clauses.h ../ladr/clause_misc.h ../ladr/ioutil.h ../ladr/ladr.h ../ladr/clock.h ../ladr/subsume.h ../ladr/di_tree.h ../ladr/subsume.h ../ladr/clock.h ../ladr/parautil.h ../ladr/clist.h ../ladr/ioutil.h

utilities.o:   	utilities.h search-structures.h

provers.o:   	provers.h search.h search-structures.h semantics.h pred_elim.h demodulate.h index_lits.h forward_subsume.h unfold.h actions.h giv_select.h white_black.h utilities.h ../ladr/interp.h ../ladr/ioutil.h ../ladr/subsume.h ../ladr/resolve.h ../ladr/clauses.h ../ladr/clause_misc.h ../ladr/ioutil.h ../ladr/ladr.h ../ladr/clock.h ../ladr/subsume.h ../ladr/di_tree.h ../ladr/subsume.h ../ladr/clock.h ../ladr/parautil.h ../ladr/clist.h ../ladr/ioutil.h

foffer.o:   	foffer.h search.h search-structures.h semantics.h pred_elim.h demodulate.h index_lits.h forward_subsume.h unfold.h actions.h giv_select.h white_black.h utilities.h ../ladr/interp.h ../ladr/ioutil.h ../ladr/subsume.h ../ladr/resolve.h ../ladr/clauses.h ../ladr/clause_misc.h ../ladr/ioutil.h ../ladr/ladr.h ../ladr/clock.h ../ladr/subsume.h ../ladr/di_tree.h ../ladr/subsume.h ../ladr/clock.h ../ladr/parautil.h ../ladr/clist.h ../ladr/ioutil.h
