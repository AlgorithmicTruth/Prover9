# LADR/mace4.src

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
  OPTFLAGS = -O2
  _BMODE = release
endif
CFLAGS = $(XFLAGS) $(OPTFLAGS) -Wall $(PLATFORM_FLAGS)

# Build mode sentinel -- auto-clean when switching debug/release.
.build_mode: FORCE
	@echo "$(_BMODE)" > .build_mode.tmp
	@if [ ! -f .build_mode ] || ! cmp -s .build_mode.tmp .build_mode; then \
	  echo "mace4.src: build mode changed to $(_BMODE), rebuilding..."; \
	  /bin/rm -f *.o *.a; \
	  mv .build_mode.tmp .build_mode; \
	else \
	  rm -f .build_mode.tmp; \
	fi

FORCE:

OBJECTS = estack.o util.o print.o syms.o ground.o arithmetic.o select.o \
	propagate.o mstate.o negpropindex.o negprop.o ordercells.o \
	commandline.o msearch.o

all: ladr lib mace4 install

libmace4.a: .build_mode $(OBJECTS)
	$(AR_CMD) libmace4.a $(OBJECTS)

##############################################################################

lib libmace4:
	$(MAKE) libmace4.a

ladr:
	cd ../ladr && $(MAKE) libladr.a
	$(MAKE) clean

mace4: libmace4.a mace4.o $(OBJECTS)
	$(CC) $(CFLAGS) -o mace4 mace4.o libmace4.a ../ladr/libladr.a

$(OBJECTS): estack.h syms.h ground.h propagate.h mstate.h msearch.h

tags:
	etags *.c ../ladr/*.c

clean:
	/bin/rm -f *.o .build_mode

realclean:
	/bin/rm -f *.o *.a mace4 .build_mode

install:
	codesign -s - -f mace4 2>/dev/null || true
	/bin/mv mace4 ../bin
