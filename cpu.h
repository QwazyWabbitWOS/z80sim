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


#ifndef H_CPU
#define H_CPU

#include "types.h"
#include <stdio.h>

typedef enum {
	REG_NONE,
	REG_PC,
	REG_SP,
	REG_AF,
	REG_BC,
	REG_DE,
	REG_HL,
	REG_IR,
	REG_IX,
	REG_IY,
} regSpec;

typedef enum traps {
	TRAP_NONE,
	TRAP_ILLEGAL,
	TRAP_MEMORY,
	TRAP_NOEFFECT,
	TRAP_METACALL,
	TRAP_UNDOCUMENTED,
	TRAP_HALT
} trap;

logic ZilogMnemonics;	// -z or --zilog switch
logic ProtectMemory;	// -p or --protect switch
logic TrapOnHalt;		// --halt switch
logic TraceExecution;	// --trace switch
logic StopUndocumented;	// -u switch

void ResetCPU(void);	// Power-on reset Z80 state.
void InitSimulation(void);
void LoadROM(FILE* Handle);
void ProcessRefresh(void);
trap Step(void);
void Disassemble(word* Address, char *Mnemonic);
void SnapshotState(FILE* Handle);
word GetRegister(regSpec);
byte GetMemoryByte(word Address);
word GetMemoryWord(word Address);
unsigned long GetFrame(void);
void RaiseIRQ(void);
void PrintRegisters(FILE*);

#endif
