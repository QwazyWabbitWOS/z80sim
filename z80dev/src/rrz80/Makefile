TOPDIR = ./

CSRC = rrz80.c map.c
CCSRC = disasm.cc

CFLAGS += -g

BIN = rrz80

SUBDIRS = cpu

# linking is done with gcc instead of g++
# stdc++ must be included while linking with
# gcc 3.2 under CYGWIN; 2003-01-26 Bernhard
LDLIBS += -lstdc++

EXTRA_LIBS  = cpu/libz80cpu.a

#include $(TOPDIR)/Makefile.rules
