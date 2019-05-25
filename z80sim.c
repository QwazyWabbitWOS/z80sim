/*
   Z80Sim - A simulator/debugger for the Zilog Z80 processor
   Copyright (C) 2003 Lorenzo J. Lucchini

   This program is free software; you can redistribute it
   and/or modify it under the terms of the GNU General Public
   License as published by the Free Software Foundation; either
   version 2 of the License, or (at your option) any later
   version. This program is distributed in the hope that it
   will be useful, but WITHOUT ANY WARRANTY; without even the
   implied warranty of MERCHANTABILITY or FITNESS FOR A
   PARTICULAR PURPOSE. See the GNU General Public License for
   more details. You should have received a copy of the GNU
   General Public License along with this program; if not,
   write to the Free Software Foundation, Inc., 59 Temple
   Place, Suite 330, Boston, MA 02111-1307 USA
*/

#include "types.h"
#include "sizes.h"
#include "cpu.h"
#include "debug.h"
#include "symbols.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <signal.h>
#include <assert.h>


static logic SingleStepping;
static sig_atomic_t UserBreak = 0;


void Quit() {
	fprintf(stdout, "Aborting.\n");
	exit(1);
}

void Break(int Signal) {
	if (SingleStepping)
		Quit();
	fflush(stdout);
	UserBreak = 1;
}

void Usage(const char* ProgramName, const char* Message) {
	if (Message) fprintf(stdout, "%s\n\n", Message);
	fprintf(stdout, "Usage: %s [<options>] <binaryfile>\n", ProgramName);
	fprintf(stdout, "Run, debug and profile a Z80 program compiled with SDCC\n");
	fprintf(stdout, "\n<binaryfile> contains a raw Z80 program, which is loaded at\n");
	fprintf(stdout, "location 0x0000 by default.\n");
	fprintf(stdout, "<options> can be one or more of the following:\n");
	fprintf(stdout, "  --trace              shows the state of the processor after each\n");
	fprintf(stdout, "                       instruction executed\n");
	fprintf(stdout, "  -l <filename.ext>    Specifies the name of the statelog file");
	fprintf(stdout, "                       and enables statelog output. (--statelog)");
	fprintf(stdout, "  --symbols <file.sym> uses a .sym file as generated by SDCC\n");
	fprintf(stdout, "                       to learn about global symbols used in\n");
	fprintf(stdout, "                       the program\n");
	fprintf(stdout, "  --dbg <file.dbg>     uses a .dbg file as generated by MakeDBG to\n");
	fprintf(stdout, "                       be able to refer to C source code lines\n");
	fprintf(stdout, "  --protect (-p)       Protection is set for memory addresses");
	fprintf(stdout, "	                    0 through 0x3fff (16384 bytes). Simulator");
	fprintf(stdout, "                       will trap if program writes to this area.");
	fprintf(stdout, "  --undoc (-u)         Trap on undocumented instructions.");
	fprintf(stdout, "  --zilog (-z)         Outputs Zilog mnemonic output for indexed");
	fprintf(stdout, "  	                    instructions instead of default.");
	fprintf(stdout, "  --halt               Emulator stops executing when HALT instruction");
	fprintf(stdout, "                       is encountered.");
	fprintf(stdout, "\n");
	Quit();
}

void ReadFileLine(FILE* Handle, unsigned int Line, char* String) {
	unsigned int i;

	fseek(Handle, 0, SEEK_SET);
	for (i = 0; i < Line; i++)
		fgets(String, MAX_STRING, Handle);
	String[strlen(String) - 1] = '\0';
}

void Stop(word Address) {
	char Mnemonic[MAX_NAME];
	source SourceSpec;

	SingleStepping = TRUE;
	fprintf(stdout, "\nFrame %ld - Stopping at address %04x: ", GetFrame(), Address);
	Disassemble(&Address, Mnemonic);
	fprintf(stdout, "%s\n", Mnemonic);
	PrintRegisters(stdout); fprintf(stdout, "\n");
	SourceSpec = SearchSource(Address);
	if (SourceSpec.File != NULL) {
		char SourceLine[MAX_STRING];
		ReadFileLine(SourceSpec.File, SourceSpec.Line - 1, SourceLine);
		fprintf(stdout, "           %s\n", SourceLine);
		ReadFileLine(SourceSpec.File, SourceSpec.Line, SourceLine);
		fprintf(stdout, "%5d  ->  %s\n", SourceSpec.Line, SourceLine);
		ReadFileLine(SourceSpec.File, SourceSpec.Line + 1, SourceLine);
		fprintf(stdout, "           %s\n", SourceLine);
	}
	else
		fprintf(stdout, "(no C source line showable)\n");
	fflush(NULL);	// for trace file
}

int main(int argc, char* argv[]) {
	FILE* ProgramFile;
	FILE* SymbolsFile;
	FILE* DebugFile;
	FILE* StateLog;
	word InstructionAddress;
	char Mnemonic[MAX_NAME];

	int i = 0;
	ZilogMnemonics = FALSE;
	ProgramFile = SymbolsFile = DebugFile = StateLog = NULL;
	SingleStepping = TRUE;
	TraceExecution = FALSE;
	for (i = 1; i < argc; i++) {
		if (!strcmp(argv[i], "--help") ||
			!strcmp(argv[i], "-h")) {
			Usage(argv[0], NULL);
		}
		else if (!strcmp(argv[i], "--trace") ||
			!strcmp(argv[i], "-t")) {
			TraceExecution = TRUE;
			fprintf(stdout, "Tracing %s\n", TraceExecution ? "ON" : "Off");
		}
		else if (!strcmp(argv[i], "--symbols") ||
			!strcmp(argv[i], "-s")) {
			i++;
			if (i == argc)
				Usage(argv[0], "Option '--symbols' requires a parameter");
			SymbolsFile = fopen(argv[i], "r");
			if (SymbolsFile == NULL)
				fprintf(stdout, "Could not open symbols file '%s'\n", argv[i]);
		}
		else if (!strcmp(argv[i], "--dbg")) {
			i++;
			if (i == argc)
				Usage(argv[0], "Option '--dbg' requires a parameter");
			DebugFile = fopen(argv[i], "r");
			if (DebugFile == NULL)
				fprintf(stdout, "Could not open debug file '%s'", argv[i]);
		}
		else if (!strcmp(argv[i], "--halt")) {
			TrapOnHalt = TRUE;
		}
		else if (!strcmp(argv[i], "--protect") || !strcmp(argv[i], "-p")) {
			ProtectMemory = TRUE;
		}
		else if (!strcmp(argv[i], "--undoc") || !strcmp(argv[i], "-u")) {
			StopUndocumented = TRUE;
		}
		else if (!strcmp(argv[i], "--zilog") || !strcmp(argv[i], "-z")) {
			ZilogMnemonics = TRUE;
		}
		else if (!strcmp(argv[i], "--statelog") || !strcmp(argv[i], "-l")) {
			i++;
			if (i == argc)
				Usage(argv[0], "Option '--statelog' requires a parameter");
			StateLog = fopen(argv[i], "w");
			if (StateLog == NULL)
				fprintf(stdout, "Could not open state log file '%s'\n", argv[i]);
		}
		else if (argv[i][0] == '-') {
			char Error[MAX_STRING];
			sprintf(Error, "Unknown option '%s'", argv[i]);
			Usage(argv[0], Error);
		}
		else {
			ProgramFile = fopen(argv[i], "r");
			if (ProgramFile == NULL) {
				fprintf(stdout, "Could not open program file '%s'\n", argv[i + 1]);
				Quit();
			}
		}
	}
	if (ProgramFile) {
		InitSimulation();
		fprintf(stdout, "Loading program...\n");
		LoadROM(ProgramFile);
		fclose(ProgramFile);
	}
	else
		Usage(argv[0], "A valid program file must be specified");

	InitSymbols();
	if (SymbolsFile) {
		fprintf(stdout, "Loading symbols...\n");
		LoadSymbols(SymbolsFile);
		fclose(SymbolsFile);
	}

	InitDebugger();
	if (DebugFile) {
		fprintf(stdout, "Loading debug information...\n");
		LoadSourcePointers(DebugFile);
		fclose(DebugFile);
	}

	InstructionAddress = 0x0000;
	fprintf(stdout, "Starting simulation...\n");
	signal(SIGINT, Break);
	for (;;) {
		if (UserBreak == 1) {
			UserBreak = 0;
			SingleStepping = TRUE;
			Stop(InstructionAddress);
		}
		if (SingleStepping || BreakRequest()) {
			SingleStepping = Debugger();
			InstructionAddress = GetRegister(REG_PC);
			ShowTrace(InstructionAddress, Mnemonic);
		}
		else {
			InstructionAddress = GetRegister(REG_PC);
			if (TraceExecution) {
				ShowTrace(InstructionAddress, Mnemonic);
			}
		}
		if (StateLog && GetFrame() == 0) {
			SnapshotState(StateLog);	// capture frame 0
		}
		switch (Step()) {
		case TRAP_NONE:
		case TRAP_NOEFFECT:
			break;
		case TRAP_METACALL:
			fprintf(stdout, "\nTRAP: Metacall not implemented (illegal instruction)\n");
			Stop(InstructionAddress);
			break;
		case TRAP_HALT:
			fprintf(stdout, "\nTRAP: HALT instruction executed\n");
			Stop(InstructionAddress);
			break;
		case TRAP_ILLEGAL:
			fprintf(stdout, "\nTRAP: Illegal instruction executed\n");
			Stop(InstructionAddress);
			break;
		case TRAP_UNDOCUMENTED:
			fprintf(stdout, "\nTRAP: Undocumented instruction executed\n");
			Stop(InstructionAddress);
			break;
		case TRAP_MEMORY:
			fprintf(stdout, "\nTRAP: Memory protection violation\n");
			Stop(InstructionAddress);
			break;
		default:
			fprintf(stdout, "\nTRAP: Unknown exception\n");
			Stop(InstructionAddress);
			break;
		}
		if (StateLog) {
			SnapshotState(StateLog);
		}
		if (GetFrame() % 1000 == 0) RaiseIRQ();
	}
}

