CFLAGS=-Wall -O2
LDFLAGS=-O2

all: z80sim

z80sim: cpu.o debug.o eval.o parser.o symbols.o tokens.o watch.o z80sim.o

clean:
	rm -f z80sim *.o
