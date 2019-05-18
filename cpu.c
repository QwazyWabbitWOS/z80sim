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
#include "opcodes.h"
#include "symbols.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define METACALL_QUIT		0x00
#define METACALL_PUTCHARACTER	0x01
#define METACALL_GETCLOCK	0x02
#define METACALL_ENTER		0x03
#define METACALL_EXIT		0x04
#define METACALL_ENTERLEAF	0x05
#define METACALL_DUMPREGS	0x06
#define METACALL_PUTWORD	0x07
#define METACALL_WRITEPROTECT	0x08
#define METACALL_READPROTECT	0x09
#define METACALL_RWPROTECT	0x0a
#define METACALL_UNPROTECT	0x0b
#define METACALL_PUTSTRING	0x0c

#define PROTECT_WRITE		1<<0
#define PROTECT_READ		1<<1

typedef union {
	word Word;
	struct {
		byte L;
		byte H;
	} Bytes;
} reg;

inline byte ReadMemory(word Address);
void WriteMemory(word Address, byte Value);

void Push(word);
void Pop(word*);

byte Memory[SIZE_MEMORY];
short Protections[SIZE_MEMORY];

byte IReg;	//Instruction register

reg AF, SP, PC;
reg BC, DE, HL;
reg IR, IX, IY;

reg AF1;
reg BC1, DE1;
reg HL1;

logic InterruptRequest;
logic EnableInterrupts;
logic IFF1, IFF2;

logic FlagZ, FlagNZ;
logic FlagC, FlagNC;
logic FlagP, FlagPO;
logic FlagMS, FlagPS;
logic FlagN, FlagH;
logic Flag3, Flag5;		// Undocumented flags

unsigned long TStates;	// Total T-states processed
unsigned long InstructionsExecuted;

logic UsefulInstruction;

logic Indexing;	// TRUE when we decoded IX or IY opcode prefixes
logic IndirectMemoryAccess; // TRUE when register indirect mode (HL), (IX/IY) 
logic NoFlagUpdate; // TRUE to prevent flag update (EX, EXX, etc.)
logic MemoryWrite;
byte MemoryData;
word MemoryAddress;
reg* PointerReg;
byte Index;

trap Exception;

// Protect a zone of the main memory as specified by Flags
//
void ProtectRange(word Start, word End, short Flags) {
	int i;
	for (i = Start; i <= End; i++) {
		Protections[i] = Flags;
	}
}

// Return the bit specifying the sign in a 2's complement value of type 'byte'.
//
inline logic SignBit(byte Value) {
	return Value & 0x80 ? TRUE : FALSE;
}


// Return TRUE if the parity of Byte is even, otherwise FALSE.
//
inline logic Parity(byte Byte) {
	byte Temp;
	Temp = Byte;
	Temp = Temp ^ (Temp >> 4);
	Temp = Temp ^ (Temp >> 2);
	Temp = Temp ^ (Temp >> 1);
	return ((Temp & 1) != 0 ? FALSE : TRUE);
}

// Copy the contents of the Flag* logic variables into the actual F register.
//
void StoreFlags() {
	if (NoFlagUpdate) {
		NoFlagUpdate = FALSE;
		return;
	}
	assert(FlagZ == !FlagNZ);
	assert(FlagC == !FlagNC);
	assert(FlagP == !FlagPO);
	assert(FlagPS == !FlagMS);
	AF.Bytes.L = (
		(FlagC ? (1 << 0) : 0) |
		(FlagN ? (1 << 1) : 0) |
		(FlagP ? (1 << 2) : 0) |
		(Flag3 ? (1 << 3) : 0) |
		(FlagH ? (1 << 4) : 0) |
		(Flag5 ? (1 << 5) : 0) |
		(FlagZ ? (1 << 6) : 0) |
		(FlagMS ? (1 << 7) : 0)
		);
}


// Set the Flag* variables depending on the contents of Datum, except those
// that cannot be inferred from it alone. Don't set the actual F register.
// Also calculate parity and store it into FlagP/FlagPO if GiveParity==TRUE.
//
void SetFlags(byte Datum) {
	Flag3 = (Datum & 0x08) != 0;
	Flag5 = (Datum & 0x20) != 0;
	if (Datum == 0) FlagZ = 1; else FlagZ = 0;
	FlagNZ = !FlagZ;
	FlagPS = !SignBit(Datum);
	FlagMS = !FlagPS;
	FlagP = Parity(Datum);
	FlagPO = !FlagP;
}


// Add Operand to *Register, and store the result into *Register. Set the Flag*
// variables accordingly.
//
void AddByte(byte * Register, byte Operand) {
	byte Op1 = *Register, Op2 = Operand;
	long Sum;

	Sum = Op1 + Op2;
	*Register = (byte)Sum;
	SetFlags(*Register);
	FlagH = ((Op1 & 0x08) ^ (Op2 & 0x08) ^ (Sum & 0x08));
	FlagC = (Sum > (word)0xFF);
	FlagNC = !FlagC;
	FlagP = (SignBit(Op1) == SignBit(Op2) && SignBit((byte)Sum) != SignBit(Op1));
	FlagPO = !FlagP;
	FlagN = 0;
}


// Subtract Operand from *Register, and store the result into *Register. Set the Flag*
// variables accordingly.
//
void SubByte(byte * Register, byte Operand) {
	byte Op1 = *Register, Op2 = -Operand;
	long Sum;

	Sum = Op1 + Op2;
	*Register = (byte)Sum;
	SetFlags(*Register);
	FlagH = ((Op1 & 0x08) ^ (Op2 & 0x08) ^ (Sum & 0x08)) ? TRUE : FALSE;
	FlagC = (Sum > (word)0xFF);
	FlagNC = !FlagC;
	FlagP = (SignBit(Op1) == SignBit(Op2) && SignBit((byte)Sum) != SignBit(Op1));
	FlagPO = !FlagP;
	FlagN = 0;
}


// As per AddByte(), but do it for two words, and only set the flags required by
// a word addition.
//
void AddWord(word * Register, word Operand) {
	long Sum;
	Sum = *Register + Operand;
	FlagH = (((*Register) & 0x0F00) + (Operand & 0x0F00) > 0x0F00) ? TRUE : FALSE;
	*Register = (word)Sum;
	FlagC = (Sum > 0xFFFF);
	FlagNC = !FlagC;
	FlagN = 0;
}

// As per AddWord(), but negate Operand before summing.
//
void SubWord(word * Register, word Operand) {
	long Sum;
	Operand = -Operand;
	Sum = *Register + Operand;
	FlagH = (((*Register) & 0x0F00) + (Operand & 0x0F00) > 0x0F00) ? TRUE : FALSE;
	*Register = (word)Sum;
	FlagC = (Sum < 0xFFFF);
	FlagNC = !FlagC;
	FlagN = 0;
}

// Logical And of two bytes, store result into *Register and set the Flag*s.
//
void And(byte * Register, byte Operand) {
	*Register = *Register & Operand;
	SetFlags(*Register);
	FlagC = 0;
	FlagNC = !FlagC;
	FlagN = 0;
	FlagH = 1;
}


// Logical exclusive Or of two bytes, store result into *Register and set the Flag*s.
//
void XOr(byte * Register, byte Operand) {
	*Register = *Register ^ Operand;
	SetFlags(*Register);
	FlagC = 0;
	FlagNC = !FlagC;
	FlagN = 0;
	FlagH = 0;
}


// Logical Or of two bytes, store result into *Register and set the Flag*s.
//
void Or(byte * Register, byte Operand) {
	*Register = *Register | Operand;
	SetFlags(*Register);
	FlagC = 0;
	FlagNC = !FlagC;
	FlagN = 0;
	FlagH = 0;
}


// Subtract Operand to *Register; don't store the result anywhere, only set the Flag*s.
//
void Compare(byte * Register, byte Operand) {
	byte Temp = *Register;
	SubByte(&Temp, Operand);
	FlagN = 1;
}


// Fetch a direct operand of the length of a word (16 bits).
//
word GetWordOperand() {
	reg WordOperand;
	WordOperand.Bytes.L = ReadMemory(PC.Word++);
	WordOperand.Bytes.H = ReadMemory(PC.Word++);
	return WordOperand.Word;
}


// Branch to NewAddress.
//
void JumpAbsolute(word NewAddress) {
	PC.Word = NewAddress;
	UsefulInstruction = TRUE;
}


// Branch to PC+Index.
//
void JumpRelative(byte Index) {
	PC.Word += (word)(sbyte)Index;
	UsefulInstruction = TRUE;
}


// Store PC into the stack, then branch to ProcAddress.
//
void Call(word ProcAddress) {
	Push(PC.Word);
	JumpAbsolute(ProcAddress);
}


// Push Register into the stack.
//
void Push(word Register) {
	WriteMemory(SP.Word - 2, (Register & 0x00FF) >> 0);
	WriteMemory(SP.Word - 1, (Register & 0xFF00) >> 8);
	SP.Word -= 2;
}


// Pop a value from the stack and store it into *Register.
//
void Pop(word * Register) {
	*Register = ReadMemory(SP.Word++);
	(*Register) |= ReadMemory(SP.Word++) << 8;
}


// Swap two words.
//
void Swap(word * Reg1, word * Reg2) {
	word Temp;
	Temp = *Reg1;
	*Reg1 = *Reg2;
	*Reg2 = Temp;
}


// Return the address of the register specified in Opcode, with Opcode being
// a Z80 opcode whose bits 3..5 specify a register.
//
byte* OperandR(byte Opcode) {
	if (OPARG_R_A(Opcode)) return &AF.Bytes.H;
	if (OPARG_R_B(Opcode)) return &BC.Bytes.H;
	if (OPARG_R_C(Opcode)) return &BC.Bytes.L;
	if (OPARG_R_D(Opcode)) return &DE.Bytes.H;
	if (OPARG_R_E(Opcode)) return &DE.Bytes.L;
	if (OPARG_R_H(Opcode)) return &HL.Bytes.H;
	if (OPARG_R_L(Opcode)) return &HL.Bytes.L;
	if (OPARG_R_PHL(Opcode)) {
		IndirectMemoryAccess = TRUE;
		MemoryData = ReadMemory(PointerReg->Word + (word)(sbyte)Index);
		return &MemoryData;
	}
	fprintf(stdout, "ERROR: Unrecognized destination register\n");
	return &AF.Bytes.H;
}


// Return the address of the register specified in Opcode, with Opcode being
// a Z80 opcode whose bits 0..2 specify a register.
//
byte* OperandS(byte Opcode) {
	if (OPARG_S_A(Opcode)) return &AF.Bytes.H;
	if (OPARG_S_B(Opcode)) return &BC.Bytes.H;
	if (OPARG_S_C(Opcode)) return &BC.Bytes.L;
	if (OPARG_S_D(Opcode)) return &DE.Bytes.H;
	if (OPARG_S_E(Opcode)) return &DE.Bytes.L;
	if (OPARG_S_H(Opcode)) return &HL.Bytes.H;
	if (OPARG_S_L(Opcode)) return &HL.Bytes.L;
	if (OPARG_S_PHL(Opcode)) {
		IndirectMemoryAccess = TRUE;
		MemoryData = ReadMemory(PointerReg->Word + (word)(sbyte)Index);
		return &MemoryData;
	}
	fprintf(stdout, "ERROR: Unrecognized source register\n");
	return &AF.Bytes.H;
}


// Return the address of the register pair specified in Opcode, with Opcode
// being a Z80 opcode whose bits 4 and 5 specify a register pair.
//
word* OperandP(byte Opcode) {
	if (OPARG_P_BC(Opcode)) return &BC.Word;
	if (OPARG_P_DE(Opcode)) return &DE.Word;
	if (OPARG_P_HL(Opcode)) return &(PointerReg->Word);
	if (OPARG_P_SP(Opcode)) return &SP.Word;
	return NULL;
}


// Return the address of a Flag* variable as specified in Opcode, with
// Opcode being a z80 opcode whose bits 3..5 specify a flag.
//
logic* OperandF(byte Opcode) {
	if (OPARG_F_NZ(Opcode)) return &FlagNZ;
	if (OPARG_F_Z(Opcode)) return &FlagZ;
	if (OPARG_F_NC(Opcode)) return &FlagNC;
	if (OPARG_F_C(Opcode)) return &FlagC;
	if (OPARG_F_PO(Opcode)) return &FlagPO;
	if (OPARG_F_PE(Opcode)) return &FlagP;
	if (OPARG_F_PS(Opcode)) return &FlagPS;
	if (OPARG_F_MS(Opcode)) return &FlagMS;
	return NULL;
}


// As per OperandF(), but works with those opcode that only accept one
// of four flags instead of eight in bits 3 and 4
//
logic* OperandSF(byte Opcode) {
	if (OPARG_SF_NZ(Opcode)) return &FlagNZ;
	if (OPARG_SF_Z(Opcode)) return &FlagZ;
	if (OPARG_SF_NC(Opcode)) return &FlagNC;
	if (OPARG_SF_C(Opcode)) return &FlagC;
	return NULL;
}


// Store a string in Name containing the human-readable name of the flag
// which is a Flag* variable at address *Flag.
//
void NameFlag(logic * Flag, char* Name)
{
	if (Flag == &FlagNZ)
		strcpy(Name, "nz");
	else if (Flag == &FlagZ)
		strcpy(Name, "z");
	else if (Flag == &FlagNC)
		strcpy(Name, "nc");
	else if (Flag == &FlagC)
		strcpy(Name, "c");
	else if (Flag == &FlagPO)
		strcpy(Name, "po");
	else if (Flag == &FlagP)
		strcpy(Name, "pe");
	else if (Flag == &FlagPS)
		strcpy(Name, "p");
	else if (Flag == &FlagMS)
		strcpy(Name, "m");
	else
		strcpy(Name, "?f");
}


// Store a string in Name containing the human-readable name of the (byte)
// register at address *Register.
//
void NameRegister(byte * Register, char* Name) {
	if (Register == &AF.Bytes.H)
		strcpy(Name, "a");
	else if (Register == &AF.Bytes.L)
		strcpy(Name, "f");
	else if (Register == &BC.Bytes.H)
		strcpy(Name, "b");
	else if (Register == &BC.Bytes.L)
		strcpy(Name, "c");
	else if (Register == &DE.Bytes.H)
		strcpy(Name, "d");
	else if (Register == &DE.Bytes.L)
		strcpy(Name, "e");
	else if (Register == &HL.Bytes.H)
		strcpy(Name, "h");
	else if (Register == &HL.Bytes.L)
		strcpy(Name, "l");
	else if (Register == &MemoryData)
	{
		if (PointerReg == &HL)
			strcpy(Name, "(hl)");
		else if (PointerReg == &IX)
			strcpy(Name, "(ix)");
		else if (PointerReg == &IY)
			strcpy(Name, "(iy)");
		else
			strcpy(Name, "?i");
	}
	else
		strcpy(Name, "?r");
}


// Store a string in Name containing the human-readable name of the
// register pair at address *Register.
//
void NameRegisterPair(word * Register, char* Name) {
	if (Register == &AF.Word)
		strcpy(Name, "af");
	else if (Register == &BC.Word)
		strcpy(Name, "bc");
	else if (Register == &DE.Word)
		strcpy(Name, "de");
	else if (Register == &HL.Word)
		strcpy(Name, "hl");
	else if (Register == &SP.Word)
		strcpy(Name, "sp");
	else if (Register == &IX.Word)
		strcpy(Name, "ix");
	else if (Register == &IY.Word)
		strcpy(Name, "iy");
	else
		strcpy(Name, "?p");
}


// Return the contents of cell number Address in main memory.
//
inline byte ReadMemory(word Address) {
	MemoryAddress = Address;
	if (Protections[Address] & PROTECT_READ)
		Exception = TRAP_MEMORY;
	MemoryData = Memory[Address];
	return MemoryData;
}


// Write the contents of Value to cell number Address in main memory,
// if this is allowed.
//
void WriteMemory(word Address, byte Value) {
	MemoryAddress = Address;
	MemoryData = Value;
	MemoryWrite = TRUE;
	if (Protections[Address] & PROTECT_WRITE) {
		Exception = TRAP_MEMORY;
	}
	else {
		Memory[Address] = Value;
	}
}

/* Stubbed. Always returns 0 */
inline byte ReadIO(byte Port) {
	return 0;
}

void WriteIO(byte Port, byte Value) {
	fprintf(stdout, "WARNING: Writing %02x into port %02x\n", Value, Port);
}

// Power-on reset Z80 state.
void ResetCPU(void)
{
	AF.Word = 0xffff;	//This is the documented reset state for AF
	SP.Word = 0xffff;	//This is the documented reset state for SP
	IFF1 = IFF2 = 0;
	IReg = 0;
	BC.Word = 0;
	DE.Word = 0;
	HL.Word = 0;
	IR.Word = 0;
	IX.Word = 0;
	IY.Word = 0;
	PC.Word = 0;
	AF1.Word = 0;
	BC1.Word = 0;
	DE1.Word = 0;
	HL1.Word = 0;
	/* Note:
	* This flag state setup is not documented Z80 behavior on reset.
	* Per Zilog manual, AF = 0xffff at reset.
	* Real Z80 flags remain 0xff until opcode affecting flags changes them.
	* Asserts in StoreFlags function will trap in that state.
	* Initialize the emulator's flags here to accord with the state
	* of accumulator but don't touch the F register.
	*/
	SetFlags(AF.Bytes.L);
	FlagNC = !FlagC;
	TStates = 0;
	InstructionsExecuted = 0;
	fprintf(stdout, "Z80 initialized\n");
}

// Initialize the Z80 simulation.
void InitSimulation() {
	int i;

	ResetCPU();
	for (i = 0; i < 0x10000; i++) {	// 64k RAM
		Memory[i] = 0x00;
	}
	//ProtectRange(0x0000, 0x3fff, PROTECT_WRITE);
	ProtectRange(0x0000, 0xffff, 0);
	fprintf(stdout, "Simulation initialized\n");
}

// Load the memory from the specified file
void LoadROM(FILE * Handle) {
	fread(Memory, 1, 0x10000, Handle);
}

void MetaCall(byte Number) {
	byte s;
	word address;
	switch (Number) {
	case METACALL_ENTER:
		// to be implemented
		break;
	case METACALL_EXIT:
		// to be implemented
		break;
	case METACALL_PUTCHARACTER:
		fprintf(stderr, "%c", HL.Bytes.L);
		fflush(stderr);
		break;
	case METACALL_PUTSTRING:
		address = HL.Word;
		while ((s = ReadMemory((address)++)))
			fprintf(stderr, "%c", (int)s);
		fprintf(stderr, "\n");
		fflush(stderr);
		break;
	case METACALL_PUTWORD:
		fprintf(stderr, "%04x", HL.Word);
		fflush(stderr);
		break;
	case METACALL_WRITEPROTECT:
		ProtectRange(HL.Word, DE.Word, PROTECT_WRITE);
		break;
	case METACALL_READPROTECT:
		ProtectRange(HL.Word, DE.Word, PROTECT_READ);
		break;
	case METACALL_RWPROTECT:
		ProtectRange(HL.Word, DE.Word, PROTECT_WRITE | PROTECT_READ);
		break;
	case METACALL_UNPROTECT:
		ProtectRange(HL.Word, DE.Word, 0);
		break;
	default:
		fprintf(stdout, "WARNING: Unimplemented metacall %02x\n", Number);
		Exception = TRAP_METACALL;
	}
	UsefulInstruction = TRUE;
}

// Log the state of the simulation to a file
void SnapshotState(FILE * Handle) {
	char Mnemonic[MAX_NAME];
	word InstructionAddress;
	InstructionAddress = PC.Word;
	fprintf(Handle, "Frame %ld Begin\n", InstructionsExecuted);
	fprintf(Handle, "\tPC <0x%04x> SP <0x%04x> ", PC.Word, SP.Word);
	fprintf(Handle, "Flags <%c%c%c%c%c%c%c%c>\n",
		(AF.Bytes.L >> 7 & 1) ? 'S' : '-', (AF.Bytes.L >> 6 & 1) ? 'Z' : '-',
		(AF.Bytes.L >> 5 & 1) ? '5' : '-', (AF.Bytes.L >> 4 & 1) ? 'H' : '-',
		(AF.Bytes.L >> 3 & 1) ? '3' : '-', (AF.Bytes.L >> 2 & 1) ? 'P' : '-',
		(AF.Bytes.L >> 1 & 1) ? 'N' : '-', (AF.Bytes.L >> 0 & 1) ? 'C' : '-');
	fprintf(Handle, "\tAF  <0x%04x> ", AF.Word);
	fprintf(Handle, "BC  <0x%04x> DE  <0x%04x> ", BC.Word, DE.Word);
	fprintf(Handle, "HL  <0x%04x>\n", HL.Word);
	fprintf(Handle, "\tAF' <0x%04x> ", AF1.Word);
	fprintf(Handle, "BC' <0x%04x> DE' <0x%04x> ", BC1.Word, DE1.Word);
	fprintf(Handle, "HL' <0x%04x>\n", HL1.Word);
	fprintf(Handle, "\tIX  <0x%04x> IY  <0x%04x> IR  <0x%04x>\n", IX.Word, IY.Word, IR.Word);
	fprintf(Handle, "\tMAR <0x%04x> MDR <0x%02x> ", MemoryAddress, MemoryData);
	fprintf(Handle, "Store <%s>\n", (MemoryWrite) ? "TRUE" : "FALSE");
	//fprintf(Handle, "\tStack <0x%02x%02x>\n",
	//	Memory[(word)(SP.Word + 1)], Memory[(word)(SP.Word + 0)]);
	fprintf(Handle, "\tTStates <%lu>\n", TStates);
	Disassemble(&InstructionAddress, Mnemonic);
	fprintf(Handle, "\tNext mnemonic <%s>\n", Mnemonic);
	fprintf(Handle, "End\n");
}


void PrintRegisters(FILE * Handle) {
	fprintf(Handle,
		"AF :%04x BC :%04x DE :%04x HL :%04x IX:%04x IY:%04x IR:%04x "
		"F: %c%c%c%c%c%c%c%c \n"
		"AF':%04x BC':%04x DE':%04x HL':%04x IFF1:%d IFF2:%d SP:%04x",
		AF.Word, BC.Word, DE.Word, HL.Word, IX.Word, IY.Word, IR.Word,
		(AF.Bytes.L >> 7 & 1) ? 'S' : '-', (AF.Bytes.L >> 6 & 1) ? 'Z' : '-',
		(AF.Bytes.L >> 5 & 1) ? '5' : '-', (AF.Bytes.L >> 4 & 1) ? 'H' : '-',
		(AF.Bytes.L >> 3 & 1) ? '3' : '-', (AF.Bytes.L >> 2 & 1) ? 'P' : '-',
		(AF.Bytes.L >> 1 & 1) ? 'N' : '-', (AF.Bytes.L >> 0 & 1) ? 'C' : '-',
		AF1.Word, BC1.Word, DE1.Word, HL1.Word, IFF1, IFF2, SP.Word);
}


word FetchAddress(word * Address) {
	word target;
	target = Memory[(*Address)++];
	target += Memory[(*Address)++] << 8;
	return target;
}

// Disassemble the Z80 instruction starting at Address.
// return the disassembly string in Mnemonic
void Disassemble(word * Address, char* Mnemonic) {
	char NameR[MAX_NAME], NameS[MAX_NAME],
		NameP[MAX_NAME], NameI[MAX_NAME],
		NameF[MAX_NAME], Symbol[MAX_NAME];
	byte Opcode;
	Opcode = Memory[(*Address)++];
	if (OP_IXPREFIX(Opcode)) {
		Opcode = ReadMemory((*Address)++);
		PointerReg = &IX;
		Indexing = TRUE;
	}
	else if (OP_IYPREFIX(Opcode)) {
		Opcode = ReadMemory((*Address)++);
		PointerReg = &IY;
		Indexing = TRUE;
	}
	else {
		PointerReg = &HL;
		Indexing = FALSE;
	}
	if (OP_HLT(Opcode)) {
		sprintf(Mnemonic, "halt");
	}
	else if (OP_DAA(Opcode)) {
		sprintf(Mnemonic, "daa");
	}
	else if (OP_LD_R_S(Opcode)) {
		NameRegister(OperandR(Opcode), NameR);
		NameRegister(OperandS(Opcode), NameS);
		if (Indexing) {
			NameRegisterPair(&PointerReg->Word, NameI);
			if (OPARG_R_PHL(Opcode)) {
				if (ZilogMnemonics)
					sprintf(Mnemonic, "ld (%s + 0x%02x), %s", NameI, Memory[(*Address)++], NameS);
				else
					sprintf(Mnemonic, "ld 0x%02x %s, %s", Memory[(*Address)++], NameR, NameS);
			}
			else if (OPARG_S_PHL(Opcode)) {
				if (ZilogMnemonics)
					sprintf(Mnemonic, "ld %s, (%s + 0x%02x)", NameR, NameI, Memory[(*Address)++]);
				else
					sprintf(Mnemonic, "ld %s, 0x%02x %s", NameR, Memory[(*Address)++], NameS);
			}
		}
		else sprintf(Mnemonic, "ld %s, %s", NameR, NameS);
	}
	else if (OP_LD_R_B(Opcode)) {
		NameRegister(OperandR(Opcode), NameR);
		if (Indexing) {
			byte low = Memory[(*Address)++];
			byte high = Memory[(*Address)++];
			NameRegisterPair(&PointerReg->Word, NameI);
			if (ZilogMnemonics)
				sprintf(Mnemonic, "ld (%s + 0x%02x), 0x%02x", NameI, low, high);
			else
				sprintf(Mnemonic, "ld #%02x %s, #%02x", low, NameR, high);
		}
		else
			sprintf(Mnemonic, "ld %s, 0x%02x", NameR, Memory[(*Address)++]);
	}
	else if (OP_LD_P_W(Opcode)) {
		NameRegisterPair(OperandP(Opcode), NameP);
		byte low = Memory[(*Address)++];
		byte high = Memory[(*Address)++];
		sprintf(Mnemonic, "ld %s, 0x%02x%02x", NameP, high, low);
	}
	else if (OP_LD_SP_HL(Opcode)) {
		NameRegisterPair(&PointerReg->Word, NameI);
		sprintf(Mnemonic, "ld sp, %s", NameI);
	}
	else if (OP_LD_A_PBC(Opcode)) {
		sprintf(Mnemonic, "ld a, (bc)");
	}
	else if (OP_LD_A_PDE(Opcode)) {
		sprintf(Mnemonic, "ld a, (de)");
	}
	else if (OP_LD_A_PW(Opcode)) {
		byte low = Memory[(*Address)++];
		byte high = Memory[(*Address)++];
		sprintf(Mnemonic, "ld a, (0x%02x%02x)", high, low);
	}
	else if (OP_LD_PW_A(Opcode)) {
		byte low = Memory[(*Address)++];
		byte high = Memory[(*Address)++];
		sprintf(Mnemonic, "ld (0x%02x%02x), a", high, low);
	}
	else if (OP_LD_PW_HL(Opcode)) {
		byte low = Memory[(*Address)++];
		byte high = Memory[(*Address)++];
		NameRegisterPair(OperandP(Opcode), NameP);
		sprintf(Mnemonic, "ld (0x%02x%02x), %s ", high, low, NameP);
	}
	else if (OP_LD_HL_PW(Opcode)) {
		byte low = Memory[(*Address)++];
		byte high = Memory[(*Address)++];
		NameRegisterPair(OperandP(Opcode), NameP);
		sprintf(Mnemonic, "ld %s, (0x%02x%02x)", NameP, high, low);
	}
	else if (OP_LD_PBC_A(Opcode)) {
		sprintf(Mnemonic, "ld (bc), a");
	}
	else if (OP_LD_PDE_A(Opcode)) {
		sprintf(Mnemonic, "ld (de), a");
	}
	else if (OP_ADD_S(Opcode)) {
		NameRegister(OperandS(Opcode), NameS);
		if (OPMOD_CARRYIN(Opcode)) {
			if (Indexing) {
				NameRegisterPair(&PointerReg->Word, NameI);
				if (ZilogMnemonics)
					sprintf(Mnemonic, "adc a, (%s + 0x%02x)", NameI, Memory[(*Address)++]);
				else
					sprintf(Mnemonic, "adc a, 0x%02x %s", Memory[(*Address)++], NameS);
			}
			else
				sprintf(Mnemonic, "adc a, %s", NameS);
		}
		else
			if (Indexing) {
				NameRegisterPair(&PointerReg->Word, NameI);
				if (ZilogMnemonics)
					sprintf(Mnemonic, "add a, (%s + 0x%02x)", NameI, Memory[(*Address)++]);
				else
					sprintf(Mnemonic, "add a, 0x%02x %s", Memory[(*Address)++], NameS);
			}
			else
				sprintf(Mnemonic, "add a, %s", NameS);
	}
	else if (OP_ADD_B(Opcode)) {
		if (OPMOD_CARRYIN(Opcode))
			sprintf(Mnemonic, "adc a, 0x%02x", Memory[(*Address)++]);
		else
			sprintf(Mnemonic, "add a, 0x%02x", Memory[(*Address)++]);
	}
	else if (OP_SUB_S(Opcode)) {
		NameRegister(OperandS(Opcode), NameS);
		if (OPMOD_CARRYIN(Opcode))
			if (Indexing) {
				NameRegisterPair(&PointerReg->Word, NameI);
				if (ZilogMnemonics)
					sprintf(Mnemonic, "sbc a, (%s + 0x%02x)", NameI, Memory[(*Address)++]);
				else
					sprintf(Mnemonic, "sbc a, 0x%02x %s", Memory[(*Address)++], NameS);
			}
			else
				sprintf(Mnemonic, "sbc a, %s", NameS);
		else
			if (Indexing) {
				NameRegisterPair(&PointerReg->Word, NameI);
				if (ZilogMnemonics)
					sprintf(Mnemonic, "sub a, (%s + 0x%02x)", NameI, Memory[(*Address)++]);
				else
					sprintf(Mnemonic, "sub a, 0x%02x %s", Memory[(*Address)++], NameS);
			}
			else
				sprintf(Mnemonic, "sub a, %s", NameS);
	}
	else if (OP_SUB_B(Opcode)) {
		if (OPMOD_CARRYIN(Opcode))
			sprintf(Mnemonic, "sbc a, 0x%02x", Memory[(*Address)++]);
		else
			sprintf(Mnemonic, "sub a, 0x%02x", Memory[(*Address)++]);
	}
	else if (OP_ADD_HL_P(Opcode)) {
		NameRegisterPair(&PointerReg->Word, NameI);
		NameRegisterPair(OperandP(Opcode), NameP);
		sprintf(Mnemonic, "add %s, %s", NameI, NameP);
	}
	else if (OP_INC_R(Opcode)) {
		NameRegister(OperandR(Opcode), NameR);
		if (Indexing) {
			NameRegisterPair(&PointerReg->Word, NameI);
			if (ZilogMnemonics)
				sprintf(Mnemonic, "inc (%s + 0x%02x)", NameI, Memory[(*Address)++]);
			else
				sprintf(Mnemonic, "inc 0x%02x %s", Memory[(*Address)++], NameR);
		}
		else
			sprintf(Mnemonic, "inc %s", NameR);
	}
	else if (OP_DEC_R(Opcode)) {
		NameRegister(OperandR(Opcode), NameR);
		if (Indexing) {
			NameRegisterPair(&PointerReg->Word, NameI);
			if (ZilogMnemonics)
				sprintf(Mnemonic, "dec (%s + 0x%02x)", NameI, Memory[(*Address)++]);
			else
				sprintf(Mnemonic, "dec 0x%02x %s", Memory[(*Address)++], NameR);
		}
		else
			sprintf(Mnemonic, "dec %s", NameR);
	}
	else if (OP_INC_P(Opcode)) {
		NameRegisterPair(OperandP(Opcode), NameP);
		sprintf(Mnemonic, "inc %s", NameP);
	}
	else if (OP_DEC_P(Opcode)) {
		NameRegisterPair(OperandP(Opcode), NameP);
		sprintf(Mnemonic, "dec %s", NameP);
	}
	else if (OP_AND_S(Opcode)) {
		NameRegister(OperandS(Opcode), NameS);
		if (Indexing) {
			NameRegisterPair(&PointerReg->Word, NameI);
			if (ZilogMnemonics)
				sprintf(Mnemonic, "and a, (%s + 0x%02x)", NameI, Memory[(*Address)++]);
			else
				sprintf(Mnemonic, "and a, 0x%02x %s", Memory[(*Address)++], NameS);
		}
		else
			sprintf(Mnemonic, "and a, %s", NameS);
	}
	else if (OP_AND_B(Opcode)) {
		sprintf(Mnemonic, "and a, 0x%02x", Memory[(*Address)++]);
	}
	else if (OP_XOR_S(Opcode)) {
		NameRegister(OperandS(Opcode), NameS);
		if (Indexing) {
			NameRegisterPair(&PointerReg->Word, NameI);
			if (ZilogMnemonics)
				sprintf(Mnemonic, "xor a, (%s + 0x%02x)", NameI, Memory[(*Address)++]);
			else
				sprintf(Mnemonic, "xor a, 0x%02x %s", Memory[(*Address)++], NameS);
		}
		else
			sprintf(Mnemonic, "xor a, %s", NameS);
	}
	else if (OP_XOR_B(Opcode)) {
		sprintf(Mnemonic, "xor a, 0x%02x", Memory[(*Address)++]);
	}
	else if (OP_OR_S(Opcode)) {
		NameRegister(OperandS(Opcode), NameS);
		if (Indexing) {
			NameRegisterPair(&PointerReg->Word, NameI);
			if (ZilogMnemonics)
				sprintf(Mnemonic, "or a, (%s + 0x%02x)", NameI, Memory[(*Address)++]);
			else
				sprintf(Mnemonic, "or a, 0x%02x %s", Memory[(*Address)++], NameS);
		}
		else
			sprintf(Mnemonic, "or a, %s", NameS);
	}
	else if (OP_OR_B(Opcode)) {
		sprintf(Mnemonic, "or a, 0x%02x", Memory[(*Address)++]);
	}
	else if (OP_CP_S(Opcode)) {
		NameRegister(OperandS(Opcode), NameS);
		if (Indexing) {
			NameRegisterPair(&PointerReg->Word, NameI);
			if (ZilogMnemonics)
				sprintf(Mnemonic, "cp (%s + 0x%02x)", NameI, Memory[(*Address)++]);
			else
				sprintf(Mnemonic, "cp a, 0x%02x %s", Memory[(*Address)++], NameS);
		}
		else
			sprintf(Mnemonic, "cp a, %s", NameS);
	}
	else if (OP_CP_B(Opcode)) {
		sprintf(Mnemonic, "cp a, 0x%02x", Memory[(*Address)++]);
	}
	else if (OP_JP_W(Opcode)) {
		LookupSymbol(FetchAddress(Address), Symbol);
		sprintf(Mnemonic, "jp %s", Symbol);
	}
	else if (OP_JP_F_W(Opcode)) {
		NameFlag(OperandF(Opcode), NameF);
		LookupSymbol(FetchAddress(Address), Symbol);
		sprintf(Mnemonic, "jp %s, %s", NameF, Symbol);
	}
	else if (OP_JP_PHL(Opcode)) {
		NameRegisterPair(&PointerReg->Word, NameI);
		sprintf(Mnemonic, "jp (%s)", NameI);
	}
	else if (OP_JR_B(Opcode)) {
		sprintf(Mnemonic, "jr 0x%02x", Memory[(*Address)++]);
	}
	else if (OP_JR_SF_B(Opcode)) {
		NameFlag(OperandF(Opcode), NameF);
		sprintf(Mnemonic, "jr %s, 0x%02x", NameF, Memory[(*Address)++]);
	}
	else if (OP_DJNZ_B(Opcode)) {
		sprintf(Mnemonic, "djnz 0x%02x", Memory[(*Address)++]);
	}
	else if (OP_CPL(Opcode)) {
		sprintf(Mnemonic, "cpl");
	}
	else if (OP_CCF(Opcode)) {
		sprintf(Mnemonic, "ccf");
	}
	else if (OP_SCF(Opcode)) {
		sprintf(Mnemonic, "scf");
	}
	else if (OP_DI(Opcode)) {
		sprintf(Mnemonic, "di");
	}
	else if (OP_EI(Opcode)) {
		sprintf(Mnemonic, "ei");
	}
	else if (OP_CALL_W(Opcode)) {
		LookupSymbol(FetchAddress(Address), Symbol);
		sprintf(Mnemonic, "call %s", Symbol);
	}
	else if (OP_CALL_F_W(Opcode)) {
		NameFlag(OperandF(Opcode), NameF);
		LookupSymbol(FetchAddress(Address), Symbol);
		sprintf(Mnemonic, "call %s, %s", NameF, Symbol);
	}
	else if (OP_RET(Opcode)) {
		sprintf(Mnemonic, "ret");
	}
	else if (OP_RET_F(Opcode)) {
		NameFlag(OperandF(Opcode), NameF);
		sprintf(Mnemonic, "ret %s", NameF);
	}
	else if (OP_EXDEHL(Opcode)) {
		sprintf(Mnemonic, "ex de, hl");
	}
	else if (OP_EXPSPHL(Opcode)) {
		sprintf(Mnemonic, "ex (sp), hl");
	}
	else if (OP_EXAFAF1(Opcode)) {
		sprintf(Mnemonic, "ex af, af'");
	}
	else if (OP_EXX(Opcode)) {
		sprintf(Mnemonic, "exx");
	}
	else if (OP_PUSH_P(Opcode)) {
		if (OperandP(Opcode) == &SP.Word)
			strcpy(NameP, "AF");
		else
			NameRegisterPair(OperandP(Opcode), NameP);
		sprintf(Mnemonic, "push %s", NameP);
	}
	else if (OP_POP_P(Opcode)) {
		if (OperandP(Opcode) == &SP.Word)
			strcpy(NameP, "AF");
		else
			NameRegisterPair(OperandP(Opcode), NameP);
		sprintf(Mnemonic, "pop %s", NameP);
	}
	else if (OP_RLA(Opcode)) {
		sprintf(Mnemonic, "rla");
	}
	else if (OP_RLCA(Opcode)) {
		sprintf(Mnemonic, "rlca");
	}
	else if (OP_RRCA(Opcode)) {
		sprintf(Mnemonic, "rrca");
	}
	else if (OP_RRA(Opcode)) {
		sprintf(Mnemonic, "rra");
	}
	else if (OP_IN_B(Opcode)) {
		if (ZilogMnemonics)
			sprintf(Mnemonic, "in a, (%02x)", Memory[(*Address)++]);
		else
			sprintf(Mnemonic, "in a, %02x", Memory[(*Address)++]);
	}
	else if (OP_OUT_B(Opcode)) {
		if (ZilogMnemonics)
			sprintf(Mnemonic, "out (%02x), a", Memory[(*Address)++]);
		else
			sprintf(Mnemonic, "out %02x, a", Memory[(*Address)++]);
	}
	else if (OP_RST00(Opcode)) {
		sprintf(Mnemonic, "rst 0x00");
	}
	else if (OP_RST08(Opcode)) {
		sprintf(Mnemonic, "rst 0x08 (META)");
	}
	else if (OP_RST10(Opcode)) {
		sprintf(Mnemonic, "rst 0x10");
	}
	else if (OP_RST18(Opcode)) {
		sprintf(Mnemonic, "rst 0x18");
	}
	else if (OP_RST20(Opcode)) {
		sprintf(Mnemonic, "rst 0x20");
	}
	else if (OP_RST28(Opcode)) {
		sprintf(Mnemonic, "rst 0x28");
	}
	else if (OP_RST30(Opcode)) {
		sprintf(Mnemonic, "rst 0x30");
	}
	else if (OP_RST38(Opcode)) {
		sprintf(Mnemonic, "rst 0x38");
	}
	else if (OP_NOP(Opcode)) {
		sprintf(Mnemonic, "nop");
	}
	else if (OP_CB(Opcode)) {
		if (!Indexing) {		//CBxx opcodes
			Opcode = Memory[(*Address)++];
			if (OP_CB_RLC(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "rlc %s", NameS);
			}
			else if (OP_CB_RRC(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "rrc %s", NameS);
			}
			else if (OP_CB_RL(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "rl %s", NameS);
			}
			else if (OP_CB_RR(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "rr %s", NameS);
			}
			else if (OP_CB_SLA(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "sla %s", NameS);
			}
			else if (OP_CB_SRA(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "sra %s", NameS);
			}
			else if (OP_CB_SLL(Opcode)) {	// undocumented Shift Left Logical
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "sll %s", NameS);
			}
			else if (OP_CB_SRL(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "srl %s", NameS);
			}
			else if (OP_CB_BIT_N_S(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "bit %d, %s", OPPARM_N(Opcode) >> 3, NameS);
			}
			else if (OP_CB_BIT_RES(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "res %d, %s", OPPARM_N(Opcode) >> 3, NameS);
			}
			else if (OP_CB_BIT_SET(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				sprintf(Mnemonic, "set %d, %s", OPPARM_N(Opcode) >> 3, NameS);
			}
			else {
				sprintf(Mnemonic, "??? OP_CB 0x%02x", Opcode);	// undecoded CBxx
			}
		}
		/* Most of these are undocumented but we disassemble them anyway.
		 Many assemblers implement the undocumented instructions.
		 Normally, no C compiler will produce them.
		 A nice instruction set table can be found at http://www.clrhome.org/table/
		 */
		else {  // Indexing && Opcode == CB
			byte offset = Memory[(*Address)++];
			Opcode = Memory[(*Address)++];
			NameRegisterPair(&PointerReg->Word, NameI);
			if (OP_CB_RLC(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				if (Opcode == 0x06)
					if (ZilogMnemonics)
						sprintf(Mnemonic, "rlc (%s + 0x%02x)", NameI, offset);
					else
						sprintf(Mnemonic, "rlc 0x%02x (%s)", offset, NameI);
				else
					sprintf(Mnemonic, "rlc (%s) 0x%02x, %s", NameI, offset, NameS);
			}
			else if (OP_CB_RRC(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				if (Opcode == 0x0e)
					if (ZilogMnemonics)
						sprintf(Mnemonic, "rrc (%s + 0x%02x)", NameI, offset);
					else
						sprintf(Mnemonic, "rrc 0x%02x (%s)", offset, NameI);
				else
					sprintf(Mnemonic, "rrc (%s) 0x%02x, %s", NameI, offset, NameS);
			}
			else if (OP_CB_RL(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				if (Opcode == 0x16)
					if (ZilogMnemonics)
						sprintf(Mnemonic, "rl (%s + 0x%02x)", NameI, offset);
					else
						sprintf(Mnemonic, "rl 0x%02x (%s)", offset, NameI);
				else
					sprintf(Mnemonic, "rl (%s) 0x%02x, %s", NameI, offset, NameS);
			}
			else if (OP_CB_RR(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				if (Opcode == 0x1e)
					if (ZilogMnemonics)
						sprintf(Mnemonic, "rr (%s + 0x%02x)", NameI, offset);
					else
						sprintf(Mnemonic, "rr 0x%02x (%s)", offset, NameI);
				else
					sprintf(Mnemonic, "rr (%s) 0x%02x, %s", NameI, offset, NameS);
			}
			else if (OP_CB_SLA(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				if (Opcode == 0x26)
					if (ZilogMnemonics)
						sprintf(Mnemonic, "sla (%s + 0x%02x)", NameI, offset);
					else
						sprintf(Mnemonic, "sla 0x%02x (%s)", offset, NameI);
				else
					sprintf(Mnemonic, "sla (%s) 0x%02x, %s", NameI, offset, NameS);
			}
			else if (OP_CB_SRA(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				if (Opcode == 0x2e)
					if (ZilogMnemonics)
						sprintf(Mnemonic, "sra (%s + 0x%02x)", NameI, offset);
					else
						sprintf(Mnemonic, "sra 0x%02x (%s)", offset, NameI);
				else
					sprintf(Mnemonic, "sra (%s) 0x%02x, %s", NameI, offset, NameS);
			}
			else if (OP_CB_SLL(Opcode)) {	// undocumented Shift Left Logical
				NameRegister(OperandS(Opcode), NameS);
				if (Opcode == 0x36)
					if (ZilogMnemonics)
						sprintf(Mnemonic, "sll (%s + 0x%02x)", NameI, offset);
					else
						sprintf(Mnemonic, "sll 0x%02x (%s)", offset, NameI);
				else
					if (ZilogMnemonics)
						sprintf(Mnemonic, "sll (%s + 0x%02x), %s", NameI, offset, NameS);
					else
						sprintf(Mnemonic, "sll 0x%02x (%s), %s", offset, NameI, NameS);
			}
			else if (OP_CB_SRL(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				if (Opcode == 0x3e)
					if (ZilogMnemonics)
						sprintf(Mnemonic, "srl (%s + 0x%02x)", NameI, offset);
					else
						sprintf(Mnemonic, "srl 0x%02x (%s)", offset, NameI);
				else
					sprintf(Mnemonic, "srl (%s) 0x%02x, %s", NameI, offset, NameS);
			}
			else if (OP_CB_BIT_N_S(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				NameRegisterPair(&PointerReg->Word, NameI);
				if (ZilogMnemonics)
					sprintf(Mnemonic, "bit %d, (%s + 0x%02x)", OPPARM_N(Opcode) >> 3, NameI, offset);
				else
					sprintf(Mnemonic, "bit %d, 0x%02x %s", OPPARM_N(Opcode) >> 3, offset, NameS);
			}
			else if (OP_CB_BIT_RES(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				NameRegisterPair(&PointerReg->Word, NameI);
				if (ZilogMnemonics)
					sprintf(Mnemonic, "res %d, (%s + 0x%02x)", OPPARM_N(Opcode) >> 3, NameI, offset);
				else
					sprintf(Mnemonic, "res %d, 0x%02x %s", OPPARM_N(Opcode) >> 3, offset, NameS);
			}
			else if (OP_CB_BIT_SET(Opcode)) {
				NameRegister(OperandS(Opcode), NameS);
				NameRegisterPair(&PointerReg->Word, NameI);
				if (ZilogMnemonics)
					sprintf(Mnemonic, "set %d, (%s + 0x%02x)", OPPARM_N(Opcode) >> 3, NameI, offset);
				else
					sprintf(Mnemonic, "set %d, 0x%02x %s", OPPARM_N(Opcode) >> 3, offset, NameS);
			}
			else {
				Opcode = Memory[(*Address)++]; // Any undecoded DDCBddxx or FDCBddxx
				sprintf(Mnemonic, "??? DD/FD CB 0x%02x 0x%02x", Opcode, Memory[(*Address)++]);
			}
		}
	}
	else if (OP_ED(Opcode)) {
		Opcode = Memory[(*Address)++];
		if (OP_ED_LD_P_PW(Opcode)) {
			NameRegisterPair(OperandP(Opcode), NameP);
			LookupSymbol(FetchAddress(Address), Symbol);
			sprintf(Mnemonic, "ld %s, (%s)", NameP, Symbol);
		}
		else if (OP_ED_LD_PW_P(Opcode)) {
			NameRegisterPair(OperandP(Opcode), NameP);
			LookupSymbol(FetchAddress(Address), Symbol);
			sprintf(Mnemonic, "ld (%s), %s", Symbol, NameP);
		}
		else if (OP_ED_ADC_HL_P(Opcode)) {
			NameRegisterPair(OperandP(Opcode), NameP);
			sprintf(Mnemonic, "adc hl, %s", NameP);
		}
		else if (OP_ED_SBC_HL_P(Opcode)) {
			NameRegisterPair(OperandP(Opcode), NameP);
			sprintf(Mnemonic, "sbc hl, %s", NameP);
		}
		else if (OP_ED_R_A(Opcode)) {
			sprintf(Mnemonic, "ld r, a");
		}
		else if (OP_ED_I_A(Opcode)) {
			sprintf(Mnemonic, "ld i, a");
		}
		else if (OP_ED_A_I(Opcode)) {
			sprintf(Mnemonic, "ld a, i");
		}
		else if (OP_ED_A_R(Opcode)) {
			sprintf(Mnemonic, "ld a, r");
		}
		else if (OP_ED_CPD(Opcode)) {
			sprintf(Mnemonic, "cpd");
		}
		else if (OP_ED_CPDR(Opcode)) {
			sprintf(Mnemonic, "cpdr");
		}
		else if (OP_ED_CPI(Opcode)) {
			sprintf(Mnemonic, "cpi");
		}
		else if (OP_ED_CPIR(Opcode)) {
			sprintf(Mnemonic, "cpir");
		}
		else if (OP_ED_RETI(Opcode)) {
			sprintf(Mnemonic, "reti");
		}
		else if (OP_ED_RETN(Opcode)) {
			sprintf(Mnemonic, "retn");
		}
		else if (OP_ED_RRD(Opcode)) { // rotate digit right through (HL)
			sprintf(Mnemonic, "rrd");
		}
		else if (OP_ED_RLD(Opcode)) { // rotate digit left through (HL)
			sprintf(Mnemonic, "rld");
		}
		else if (OP_ED_IM0(Opcode)) {
			sprintf(Mnemonic, "im 0");
		}
		else if (OP_ED_IM1(Opcode)) {
			sprintf(Mnemonic, "im 1");
		}
		else if (OP_ED_IM2(Opcode)) {
			sprintf(Mnemonic, "im 2");
		}
		else if (OP_ED_IND(Opcode)) {
			sprintf(Mnemonic, "ind");
		}
		else if (OP_ED_INDR(Opcode)) {
			sprintf(Mnemonic, "indr");
		}
		else if (OP_ED_INI(Opcode)) {
			sprintf(Mnemonic, "ini");
		}
		else if (OP_ED_INIR(Opcode)) {
			sprintf(Mnemonic, "inir");
		}
		else if (OP_ED_LDD(Opcode)) {
			sprintf(Mnemonic, "ldd");
		}
		else if (OP_ED_LDDR(Opcode)) {
			sprintf(Mnemonic, "lddr");
		}
		else if (OP_ED_LDI(Opcode)) {
			sprintf(Mnemonic, "ldi");
		}
		else if (OP_ED_LDIR(Opcode)) {
			sprintf(Mnemonic, "ldir");
		}
		else if (OP_ED_NEG(Opcode)) {
			sprintf(Mnemonic, "neg");
		}
		else if (OP_ED_OUTI(Opcode)) {
			sprintf(Mnemonic, "outi");
		}
		else if (OP_ED_OTIR(Opcode)) {
			sprintf(Mnemonic, "otir");
		}
		else if (OP_ED_OUTD(Opcode)) {
			sprintf(Mnemonic, "outd");
		}
		else if (OP_ED_OTDR(Opcode)) {
			sprintf(Mnemonic, "otdr");
		}
		else if (OP_ED_OUT_C_R(Opcode)) {
			NameRegister(OperandR(Opcode), NameR);
			sprintf(Mnemonic, "out (c), %s", NameR);
		}
		else if (OP_ED_IN_R_C(Opcode)) {
			NameRegister(OperandR(Opcode), NameR);
			sprintf(Mnemonic, "in %s, (c)", NameR);
		}
		else {
			// Unrecognized EDxx opcode.
			sprintf(Mnemonic, "??? OP_ED 0x%02x", Opcode);
		}
	}
	else {
		sprintf(Mnemonic, "??? OP: 0x%02x", Opcode);
	}
}


// Process an interrupt request
//
void ProcessIRQ() {
	Push(PC.Word);
	PC.Word = 0x0038;
	InterruptRequest = FALSE;
}

// Refresh increments R register by 2 every M1 cycle.
// Bit 7 is never set or cleared here. Bit 0 is always 0.
void ProcessRefresh(void)
{
	if (IR.Bytes.L == 0x7E)
		IR.Bytes.L &= 0x80;
	else
		IR.Bytes.L += 2 & 0x7e;
}

// Execute the Z80 instruction pointed to by PC.
//
trap Step() {
	reg OldAF, OldSP, OldPC, OldBC, OldDE, OldHL, OldIX, OldIY;
	logic OldIFF1, OldIFF2;
	word Word;
	byte Byte;
	Exception = TRAP_NONE;
	IReg = ReadMemory(PC.Word++);
	OldAF = AF;
	OldSP = SP;
	OldPC = PC;
	PC = OldPC; // Silence warning about unused OldPC
	OldBC = BC;
	OldDE = DE;
	OldHL = HL;
	OldIX = IX;
	OldIY = IY;
	OldIFF1 = IFF1;
	OldIFF2 = IFF2;
	Index = 0;
	UsefulInstruction = FALSE;
	IndirectMemoryAccess = FALSE;
	MemoryWrite = FALSE;

	ProcessRefresh();

	if (EnableInterrupts)
		IFF1 = TRUE;
	if (OP_IXPREFIX(IReg)) {
		IReg = ReadMemory(PC.Word++);
		PointerReg = &IX;
		Indexing = TRUE;
		TStates += 4;
	}
	else if (OP_IYPREFIX(IReg)) {
		IReg = ReadMemory(PC.Word++);
		PointerReg = &IY;
		Indexing = TRUE;
		TStates += 4;
	}
	else {
		PointerReg = &HL;
		Indexing = FALSE;
	}

	if (OP_HLT(IReg)) {
		PC.Word--;
		UsefulInstruction = TRUE;
		TStates += 4;
		if (TrapOnHalt)
			Exception = TRAP_HALT;
	}
	else if (OP_DAA(IReg)) {
		int     acc, carry, d;
		acc = AF.Bytes.H;
		if (acc > 0x99 || FlagC) {
			carry = FlagC;
			d = 0x60;
		}
		else
			carry = d = 0;
		if ((acc & 0x0f) > 0x09 || FlagH)
			d += 0x06;
		AF.Bytes.H += FlagN ? -d : +d;
		FlagMS = AF.Bytes.H & 0x80 ? TRUE : FALSE;
		FlagPS = !FlagMS;
		FlagZ = (AF.Bytes.H == 0) ? TRUE : FALSE;
		FlagNZ = !FlagZ;
		FlagP = Parity(AF.Bytes.H);
		FlagPO = !FlagP;
		FlagC = carry;
		FlagNC = !FlagC;
		TStates += 4;
	}
	else if (OP_LD_R_S(IReg)) {
		if (Indexing) {
			Index = ReadMemory(PC.Word++);
			TStates += 5;
		}
		*OperandR(IReg) = *OperandS(IReg);
		if (IndirectMemoryAccess == TRUE)
			TStates += 7;
		else
			TStates += 4;
	}
	else if (OP_LD_R_B(IReg)) {
		if (Indexing) {
			Index = ReadMemory(PC.Word++);
			TStates += 5;
		}
		*OperandR(IReg) = ReadMemory(PC.Word++);
		if (IndirectMemoryAccess == TRUE)
			TStates += 10;
		else
			TStates += 7;
	}
	else if (OP_LD_P_W(IReg)) {
		*OperandP(IReg) = ReadMemory(PC.Word++);
		*OperandP(IReg) += (ReadMemory(PC.Word++) << 8);
		TStates += 10;
	}
	else if (OP_LD_SP_HL(IReg)) {
		SP.Word = PointerReg->Word;
		TStates += 10;
	}
	else if (OP_LD_A_PBC(IReg)) {
		AF.Bytes.H = ReadMemory(BC.Word);
		TStates += 7;
	}
	else if (OP_LD_A_PDE(IReg)) {
		AF.Bytes.H = ReadMemory(DE.Word);
		TStates += 7;
	}
	else if (OP_LD_A_PW(IReg)) {
		word addr;
		addr = ReadMemory(PC.Word++);
		addr += ReadMemory(PC.Word++) << 8;
		AF.Bytes.H = ReadMemory(addr);
		TStates += 13;
	}
	else if (OP_LD_PW_A(IReg)) {
		word addr;
		addr = ReadMemory(PC.Word++);
		addr += ReadMemory(PC.Word++) << 8;
		WriteMemory(addr, AF.Bytes.H);
		TStates += 13;
	}
	else if (OP_LD_PW_HL(IReg)) {
		word Address = ReadMemory(PC.Word++);
		Address += ReadMemory(PC.Word++) << 8;
		WriteMemory(Address, PointerReg->Bytes.L);
		WriteMemory(Address + 1, PointerReg->Bytes.H);
		TStates += 16;
	}
	else if (OP_LD_HL_PW(IReg)) {
		word Address = ReadMemory(PC.Word++);
		Address += ReadMemory(PC.Word++) << 8;
		PointerReg->Word = ReadMemory(Address);
		PointerReg->Word += ReadMemory(Address + 1) << 8;
		TStates += 16;
	}
	else if (OP_LD_PBC_A(IReg)) {
		WriteMemory(BC.Word, AF.Bytes.H);
		TStates += 7;
	}
	else if (OP_LD_PDE_A(IReg)) {
		WriteMemory(DE.Word, AF.Bytes.H);
		TStates += 7;
	}
	else if (OP_ADD_S(IReg)) {	// ADD and ADC
		if (Indexing) {
			Index = ReadMemory(PC.Word++);
		}
		if (OPMOD_CARRYIN(IReg))
			AddByte(&AF.Bytes.H, *OperandS(IReg) + (FlagC ? 1 : 0));
		else
			AddByte(&AF.Bytes.H, *OperandS(IReg));
		TStates += 4;
	}
	else if (OP_ADD_B(IReg)) {
		if (OPMOD_CARRYIN(IReg))
			AddByte(&AF.Bytes.H, ReadMemory(PC.Word++) + (FlagC ? 1 : 0));
		else
			AddByte(&AF.Bytes.H, ReadMemory(PC.Word++));
		TStates += 7;
	}
	else if (OP_SUB_S(IReg)) {
		if (Indexing)
			Index = ReadMemory(PC.Word++);
		if (OPMOD_CARRYIN(IReg))
			SubByte(&AF.Bytes.H, *OperandS(IReg) + (FlagC ? 1 : 0));
		else
			SubByte(&AF.Bytes.H, *OperandS(IReg));
		FlagN = 1;
		TStates += 4;
		if (Indexing)
			TStates += 15;
	}
	else if (OP_SUB_B(IReg)) {
		if (OPMOD_CARRYIN(IReg))
			SubByte(&AF.Bytes.H, ReadMemory(PC.Word++) + (FlagC ? 1 : 0));
		else
			SubByte(&AF.Bytes.H, ReadMemory(PC.Word++));
		FlagN = 1;
		TStates += 7;
	}
	else if (OP_ADD_HL_P(IReg)) {
		AddWord(&PointerReg->Word, *OperandP(IReg));
	}
	else if (OP_INC_R(IReg)) {
		byte* Operand;
		logic Negative;
		if (Indexing)
			Index = ReadMemory(PC.Word++);
		Operand = OperandR(IReg);
		Negative = SignBit(*Operand);
		SetFlags(++(*Operand));
		FlagP = Negative ^ (SignBit(*Operand));
		FlagPO = !FlagP;
		FlagN = 0;
		TStates += 4;
	}
	else if (OP_DEC_R(IReg)) {
		if (Indexing)
			Index = ReadMemory(PC.Word++);
		SetFlags(--(*OperandR(IReg)));
		FlagN = 1;
		TStates += 4;
	}
	else if (OP_INC_P(IReg)) {
		(*OperandP(IReg))++;
		TStates += 6;
	}
	else if (OP_DEC_P(IReg)) {
		(*OperandP(IReg))--;
		TStates += 6;
	}
	else if (OP_AND_S(IReg)) {
		if (Indexing)
			Index = ReadMemory(PC.Word++);
		And(&AF.Bytes.H, *OperandS(IReg));
		TStates += 7;
	}
	else if (OP_AND_B(IReg)) {
		And(&AF.Bytes.H, ReadMemory(PC.Word++));
		TStates += 4;
	}
	else if (OP_XOR_S(IReg)) {
		if (Indexing)
			Index = ReadMemory(PC.Word++);
		XOr(&AF.Bytes.H, *OperandS(IReg));
		TStates += 4;
	}
	else if (OP_XOR_B(IReg)) {
		XOr(&AF.Bytes.H, ReadMemory(PC.Word++));
		TStates += 7;
	}
	else if (OP_OR_S(IReg)) {
		if (Indexing)
			Index = ReadMemory(PC.Word++);
		Or(&AF.Bytes.H, *OperandS(IReg));
		TStates += 4;
	}
	else if (OP_OR_B(IReg)) {
		Or(&AF.Bytes.H, ReadMemory(PC.Word++));
		TStates += 7;
	}
	else if (OP_CP_S(IReg)) {
		if (Indexing) {
			TStates += 11;	// Indexed compare takes 19 states (4,4,3,5,3)
			Index = ReadMemory(PC.Word++);
		}
		Compare(&AF.Bytes.H, *OperandS(IReg));
		TStates += 4;
	}
	else if (OP_CP_B(IReg)) {
		Compare(&AF.Bytes.H, ReadMemory(PC.Word++));
		TStates += 7;
	}
	else if (OP_JP_W(IReg)) {
		JumpAbsolute(GetWordOperand());
		TStates += 10;
	}
	else if (OP_JP_F_W(IReg)) {
		Word = GetWordOperand();
		if (*OperandF(IReg))
			JumpAbsolute(Word);
		TStates += 10;
		UsefulInstruction = TRUE;
	}
	else if (OP_JP_PHL(IReg)) {
		PC.Word = HL.Word;
		TStates += 4;
	}
	else if (OP_JR_B(IReg)) {
		JumpRelative(ReadMemory(PC.Word++));
		TStates += 12;
	}
	else if (OP_JR_SF_B(IReg)) {
		Byte = ReadMemory(PC.Word++);
		if (*OperandF(IReg)) {
			JumpRelative(Byte);
			TStates += 12;
		}
		else
			TStates += 7;
		UsefulInstruction = TRUE;
	}
	else if (OP_DJNZ_B(IReg)) {
		Byte = ReadMemory(PC.Word++);
		BC.Bytes.H--;
		if (BC.Bytes.H != 0) {
			JumpRelative(Byte);
			TStates += 13;
		}
		else
			TStates += 8;
	}
	else if (OP_CPL(IReg)) {
		AF.Bytes.H = ~AF.Bytes.H;
		FlagN = FlagH = 1;
		TStates += 4;
	}
	else if (OP_CCF(IReg)) {
		FlagH = FlagC;
		FlagC = !FlagC;
		FlagNC = !FlagNC;
		FlagN = 0;
		// Undocumented:
		Flag3 = AF.Bytes.H & 0x08;
		Flag5 = AF.Bytes.H & 0x20;
		TStates += 4;
	}
	else if (OP_SCF(IReg)) {
		FlagC = 1;
		FlagNC = !FlagC;
		FlagN = 0;
		FlagH = 0;
		// Undocumented:
		Flag3 = AF.Bytes.H & 0x08;
		Flag5 = AF.Bytes.H & 0x20;
		TStates += 4;
	}
	else if (OP_DI(IReg)) {
		IFF1 = FALSE;
		TStates += 4;
	}
	else if (OP_EI(IReg)) {
		EnableInterrupts = TRUE;
		TStates += 4;
	}
	else if (OP_CALL_W(IReg)) {
		Call(GetWordOperand());
		TStates += 17;
	}
	else if (OP_CALL_F_W(IReg)) {
		Word = GetWordOperand();
		if (*OperandF(IReg)) {
			Call(Word);
			TStates += 17;
		}
		else
			TStates += 10;
		UsefulInstruction = TRUE;
	}
	else if (OP_RET(IReg)) {
		Pop(&(PC.Word));
		TStates += 10;
	}
	else if (OP_RET_F(IReg)) {
		if (*OperandF(IReg)) {
			Pop(&PC.Word);
			TStates += 11;
		}
		else TStates += 5;
		UsefulInstruction = TRUE;
	}
	else if (OP_EXDEHL(IReg)) {
		NoFlagUpdate = TRUE;
		Swap(&DE.Word, &HL.Word);
		TStates += 4;
	}
	else if (OP_EXPSPHL(IReg)) {
		NoFlagUpdate = TRUE;
		byte TempH, TempL;
		TempL = ReadMemory((word)(SP.Word + 0));
		TempH = ReadMemory((word)(SP.Word + 1));
		WriteMemory((word)(SP.Word + 0), PointerReg->Bytes.L);
		WriteMemory((word)(SP.Word + 1), PointerReg->Bytes.H);
		PointerReg->Bytes.H = TempH;
		PointerReg->Bytes.L = TempL;
		TStates += 19;
		if (Indexing)
			TStates += 4;
	}
	else if (OP_EXAFAF1(IReg)) {
		NoFlagUpdate = TRUE;
		Swap(&AF.Word, &AF1.Word);
		TStates += 4;
	}
	else if (OP_EXX(IReg)) {
		NoFlagUpdate = TRUE;
		Swap(&BC.Word, &BC1.Word);
		Swap(&DE.Word, &DE1.Word);
		Swap(&HL.Word, &HL1.Word);
		TStates += 4;
	}
	else if (OP_PUSH_P(IReg)) {
		Push((OperandP(IReg) == &SP.Word) ? (AF.Word) : (*OperandP(IReg)));
		TStates += 11;
		if (Indexing)
			TStates += 4;
	}
	else if (OP_POP_P(IReg)) {
		if (OperandP(IReg) == &SP.Word)
			Pop(&AF.Word);
		else
			Pop(OperandP(IReg));
		TStates += 10;
		if (Indexing)
			TStates += 4;
	}
	else if (OP_RLA(IReg)) {
		logic Carry = SignBit(AF.Bytes.H);
		AF.Bytes.H = ((AF.Bytes.H) << 1) + (FlagC ? 1 : 0);
		FlagNC = !(FlagC = Carry);
		FlagN = FlagH = 0;
		TStates += 4;
	}
	else if (OP_RLCA(IReg)) {
		FlagC = SignBit(AF.Bytes.H);
		FlagNC = !FlagC;
		AF.Bytes.H = ((AF.Bytes.H) << 1) + (FlagC ? 1 : 0);
		FlagN = FlagH = 0;
		TStates += 4;
	}
	else if (OP_RRCA(IReg)) {
		FlagC = (AF.Bytes.H & 1);
		FlagNC = !FlagC;
		AF.Bytes.H = ((AF.Bytes.H) >> 1) + (FlagC ? (1 << 7) : (0 << 7));
		FlagN = FlagH = 0;
		TStates += 4;
	}
	else if (OP_RRA(IReg)) {
		logic Carry = AF.Bytes.H & 1;
		AF.Bytes.H = ((AF.Bytes.H) >> 1) + (FlagC ? (1 << 7) : (0 << 7));
		FlagNC = !(FlagC = Carry);
		FlagN = FlagH = 0;
		TStates += 4;
	}
	else if (OP_IN_B(IReg)) {
		AF.Bytes.H = ReadIO(ReadMemory(PC.Word++));
		TStates += 11;
	}
	else if (OP_OUT_B(IReg)) {
		WriteIO(ReadMemory(PC.Word++), AF.Bytes.H);
		TStates += 11;
	}
	else if (OP_RST00(IReg)) {
		Push(PC.Word);
		PC.Word = 0x0000;
		TStates += 11;
	}
	else if (OP_RST08(IReg)) {
		MetaCall(AF.Bytes.H);
		// Push(PC.Word);
		// PC.Word=0x0008;
		TStates += 11;
	}
	else if (OP_RST10(IReg)) {
		Push(PC.Word);
		PC.Word = 0x0010;
		TStates += 11;
	}
	else if (OP_RST18(IReg)) {
		Push(PC.Word);
		PC.Word = 0x0018;
		TStates += 11;
	}
	else if (OP_RST20(IReg)) {
		Push(PC.Word);
		PC.Word = 0x0020;
		TStates += 11;
	}
	else if (OP_RST28(IReg)) {
		Push(PC.Word);
		PC.Word = 0x0028;
		TStates += 11;
	}
	else if (OP_RST30(IReg)) {
		Push(PC.Word);
		PC.Word = 0x0030;
		TStates += 11;
	}
	else if (OP_RST38(IReg)) {
		Push(PC.Word);
		PC.Word = 0x0038;
		TStates += 11;
	}
	else if (OP_NOP(IReg)) {
		TStates += 4;
		UsefulInstruction = TRUE;
	}
	else if (OP_CB(IReg)) {
		TStates += 4;	// for the CB fetch
		if (Indexing) {
			Index = ReadMemory(PC.Word++);
			TStates += 4;	// for the index fetch
		}
		IReg = ReadMemory(PC.Word++);
		if (OP_CB_RLC(IReg)) {	// C <- 7..0 <- 7
			FlagC = SignBit(*OperandS(IReg));
			FlagNC = !FlagC;
			*OperandS(IReg) = ((*OperandS(IReg)) << 1) + (FlagC ? 1 : 0);
			SetFlags(*OperandS(IReg));
			TStates += 8;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_RRC(IReg)) {	// 0 -> 7..0 -> C
			FlagC = ((*OperandS(IReg)) & 0x01);
			FlagNC = !FlagC;
			*OperandS(IReg) = ((*OperandS(IReg)) >> 1) + (FlagC ? 0x80 : 0);
			SetFlags(*OperandS(IReg));
			TStates += 8;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_RL(IReg)) {	// C <- 7..0 <- C
			logic Carry = SignBit(*OperandS(IReg));
			*OperandS(IReg) = ((*OperandS(IReg)) << 1) + (FlagC ? 1 : 0);
			FlagNC = !(FlagC = Carry);
			SetFlags(*OperandS(IReg));
			TStates += 8;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_RR(IReg)) {	// C -> 7..0 -> C
			logic Carry = (*OperandS(IReg) & 0x01);
			*OperandS(IReg) = ((*OperandS(IReg)) >> 1) + (FlagC ? 1 : 0);
			FlagC = Carry;
			FlagNC = !FlagC;
			SetFlags(*OperandS(IReg));
			TStates += 8;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_SLA(IReg)) {	// C <- 7..0 <- 0
			FlagC = SignBit(*OperandS(IReg));
			FlagNC = !FlagC;
			*OperandS(IReg) = ((*OperandS(IReg)) << 1) & 0x7e;
			SetFlags(*OperandS(IReg));
			FlagN = 0;
			FlagH = 0;
			TStates += 4;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_SLL(IReg)) {	// C <- 7..0 <- 1
			FlagC = SignBit(*OperandS(IReg));
			FlagNC = !FlagC;
			*OperandS(IReg) = ((*OperandS(IReg)) << 1) | 1;
			SetFlags(*OperandS(IReg));
			FlagN = 0;
			FlagH = 0;
			TStates += 4;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_SRA(IReg)) {	// 7 -> 7..0 -> C
			byte bit7 = (SignBit(*OperandS(IReg)) << 7);
			FlagC = ((*OperandS(IReg)) & 0x01);
			FlagNC = !FlagC;
			*OperandS(IReg) = (*OperandS(IReg)) >> 1;
			*OperandS(IReg) += bit7;
			SetFlags(*OperandS(IReg));
			FlagN = 0;
			FlagH = 0;
			TStates += 4;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_SRL(IReg)) {	// 0 -> 7..0 -> C
			FlagC = ((*OperandS(IReg)) & 0x01);
			FlagNC = !FlagC;
			*OperandS(IReg) = (*OperandS(IReg)) >> 1;
			*OperandS(IReg) &= 0x7f;
			SetFlags(*OperandS(IReg));
			FlagN = 0;
			FlagH = 0;
			TStates += 4;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_BIT_N_S(IReg)) {
			FlagZ = !(FlagNZ = (*OperandS(IReg)) & (1 << (OPPARM_N(IReg) >> 3)));
			FlagN = 0;
			FlagH = 1;
			TStates += 4;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_BIT_SET(IReg)) {
			*OperandS(IReg) |= (1 << (OPPARM_N(IReg) >> 3));
			TStates += 4;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else if (OP_CB_BIT_RES(IReg)) {
			*OperandS(IReg) &= ~(1 << (OPPARM_N(IReg) >> 3));
			TStates += 4;
			if (IndirectMemoryAccess)
				TStates += 7;
		}
		else {
			fprintf(stdout, "ERROR: Unimplemented CB opcode %02x at PC = %04x\n", IReg, PC.Word - 1);
			Exception = TRAP_ILLEGAL;
			UsefulInstruction = TRUE;
		}
	}
	else if (OP_ED(IReg)) {
		IReg = ReadMemory(PC.Word++);
		if (OP_ED_LD_P_PW(IReg)) {
			int Addr;
			Addr = ReadMemory(PC.Word++);
			Addr += ReadMemory(PC.Word++) << 8;
			*OperandP(IReg) = ReadMemory(Addr++);
			*OperandP(IReg) += (ReadMemory(Addr) << 8);
			TStates += 20;
		}
		else if (OP_ED_LD_PW_P(IReg)) {	// ld (word), rr
			int Addr;
			Addr = ReadMemory(PC.Word++);
			Addr += ReadMemory(PC.Word++) << 8;
			WriteMemory(Addr++, *OperandP(IReg) & 0xff);
			WriteMemory(Addr, *OperandP(IReg) >> 8);
			TStates += 20;
		}
		else if (OP_ED_ADC_HL_P(IReg)) {	/* ADC HL, RP */
			AddWord(&PointerReg->Word, *OperandP(IReg) + (FlagC ? 1 : 0));
			FlagP = FlagC; // P/V = overflow
			FlagPO = !FlagP;
			FlagZ = (PointerReg->Word == 0);
			FlagNZ = !FlagZ;
			FlagMS = (PointerReg->Bytes.H & 0x80);
			FlagPS = !FlagMS;
			TStates += 15;
		}
		else if (OP_ED_SBC_HL_P(IReg)) {	/* SBC HL, RP */
			SubWord(&PointerReg->Word, *OperandP(IReg) - (FlagC ? 1 : 0));
			FlagP = FlagC; // P/V = overflow
			FlagPO = !FlagP;
			FlagZ = (PointerReg->Word == 0);
			FlagNZ = !FlagZ;
			FlagMS = (PointerReg->Bytes.H & 0x80);
			FlagPS = !FlagMS;
			TStates += 15;
		}
		else if (OP_ED_RRD(IReg)) {
			int     x, a;
			x = ReadMemory(HL.Word);
			a = (AF.Bytes.H & 0xf0) << 8;
			a |= ((x & 0x0f) << 8) | ((AF.Bytes.H & 0x0f) << 4) | (x >> 4);
			WriteMemory(HL.Word, a);
			a >>= 8;
			AF.Bytes.H = a;
			SetFlags(AF.Bytes.H);
			TStates += 18;
		}
		else if (OP_ED_RLD(IReg)) {
			int     x, a;
			x = ReadMemory(HL.Word);
			a = (AF.Bytes.H & 0xf0) << 8;
			a |= (x << 4) | (AF.Bytes.H & 0x0f);
			WriteMemory(HL.Word, a);
			a >>= 8;
			AF.Bytes.H = a;
			SetFlags(AF.Bytes.H);
			TStates += 18;
		}
		else if (OP_ED_R_A(IReg)) {
			IR.Bytes.L = AF.Bytes.H;
			NoFlagUpdate = TRUE;
			TStates += 9;
		}
		else if (OP_ED_A_R(IReg)) {
			AF.Bytes.H = IR.Bytes.L;
			SetFlags(AF.Bytes.H);
			FlagH = FlagN = 0;
			FlagP = IFF2;
			FlagPO = !FlagP;
			TStates += 9;
		}
		else if (OP_ED_A_I(IReg)) {
			AF.Bytes.H = IR.Bytes.H;
			SetFlags(AF.Bytes.H);
			FlagH = FlagN = 0;
			FlagP = IFF2;
			FlagPO = !FlagP;
			TStates += 9;
		}
		else if (OP_ED_I_A(IReg)) {
			IR.Bytes.H = AF.Bytes.H;
			NoFlagUpdate = TRUE;
			TStates += 9;
		}
		else if (OP_ED_RETI(IReg)) {
			puts("RETI instruction not implemented"); //TODO: Implement RETI
		}
		else if (OP_ED_RETN(IReg)) {
			puts("RETN instruction not implemented"); //TODO: Implement RETN
		}
		else if (OP_ED_IM0(IReg)) {
			puts("IM 0 instruction not implemented"); //TODO: Switch to interrupt mode 0
		}
		else if (OP_ED_IM1(IReg)) {
			puts("IM 1 instruction not implemented"); //TODO: Switch to interrupt mode 1
		}
		else if (OP_ED_IM2(IReg)) {
			puts("IM 2 instruction not implemented"); //TODO: Switch to interrupt mode 2
		}
		else if (OP_ED_IN_R_C(IReg)) {
			BC.Bytes.L = ReadIO(*OperandR(IReg));
			TStates += 12;
		}
		else if (OP_ED_OUT_C_R(IReg)) {
			WriteIO(*OperandR(IReg), BC.Bytes.L);
			TStates += 12;
		}
		else if (OP_ED_OUTI(IReg)) {
			puts("OUTI instruction not implemented");
		}
		else if (OP_ED_OTIR(IReg)) {
			puts("OTIR instruction not implemented");
		}
		else if (OP_ED_OUTD(IReg)) {
			puts("OUTD instruction not implemented");
		}
		else if (OP_ED_OTDR(IReg)) {
			puts("OTDR instruction not implemented");
		}
		else if (OP_ED_NEG(IReg)) {
			FlagC = (AF.Bytes.H != 0) ? TRUE : FALSE;
			FlagNC = !FlagC;
			FlagP = (AF.Bytes.H == 0x80) ? TRUE : FALSE;
			FlagPO = !FlagP;
			AF.Bytes.H = ~AF.Bytes.H + 1;
			FlagMS = SignBit(AF.Bytes.H);
			FlagPS = !FlagMS;
			FlagZ = (AF.Bytes.H == 0) ? TRUE : FALSE;
			FlagNZ = !FlagZ;
			FlagN = 1;
			TStates += 8;
		}
		else if (OP_ED_CPD(IReg)) { // A - (HL), HL = HL - 1, BC = BC - 1
			Compare(&AF.Bytes.H, Memory[HL.Word]);
			HL.Word -= 1;
			BC.Word -= 1;
			FlagP = BC.Word != 0 ? TRUE : FALSE;
			FlagPO = !FlagP;
			TStates += 16;
		}
		else if (OP_ED_CPDR(IReg)) {
			Compare(&AF.Bytes.H, Memory[HL.Word]);
			HL.Word -= 1;
			BC.Word -= 1;
			FlagP = BC.Word != 0 ? TRUE : FALSE;
			FlagPO = !FlagP;
			TStates += 16;
			if (FlagPO || FlagNZ) { // Repeat until A = (HL) or BC = 0
				PC.Word -= 2;
				TStates += 5;
			}
		}
		else if (OP_ED_CPI(IReg)) { // A - (HL), HL = HL + 1, BC = BC - 1
			Compare(&AF.Bytes.H, Memory[HL.Word]);
			HL.Word += 1;
			BC.Word -= 1;
			FlagP = BC.Word != 0 ? TRUE : FALSE;
			FlagPO = !FlagP;
			TStates += 16;
		}
		else if (OP_ED_CPIR(IReg)) { // A - (HL), HL = HL + 1, BC = BC - 1
			Compare(&AF.Bytes.H, Memory[HL.Word]);
			HL.Word += 1;
			BC.Word -= 1;
			FlagP = BC.Word != 0 ? TRUE : FALSE;
			FlagPO = !FlagP;
			TStates += 16;
			if (FlagPO || FlagNZ) {	// Repeat until A = (HL) or BC = 0
				PC.Word -= 2;
				TStates += 5;
			}
		}
		else {
			fprintf(stdout, "ERROR: Unimplemented ED opcode %02x at PC = %04x\n", IReg, PC.Word - 1);
			Exception = TRAP_ILLEGAL;
			UsefulInstruction = TRUE;
		}
	}
	else {
		fprintf(stdout, "ERROR: Unimplemented primary opcode %02x at PC = %04x\n", IReg, PC.Word - 1);
		Exception = TRAP_ILLEGAL;
		UsefulInstruction = TRUE;
	}

	StoreFlags();

	if (IndirectMemoryAccess) {
		MemoryAddress = PointerReg->Word + (word)(sbyte)Index;
		WriteMemory(MemoryAddress, MemoryData);
	}
	else if (!MemoryWrite && !UsefulInstruction &&
		AF.Word == OldAF.Word && BC.Word == OldBC.Word &&
		DE.Word == OldDE.Word && HL.Word == OldHL.Word &&
		IX.Word == OldIX.Word && IY.Word == OldIY.Word &&
		SP.Word == OldSP.Word && IFF1 == OldIFF1 && IFF2 == OldIFF2)
	{
		//fprintf(stderr, "WARNING: instruction %02x at %04x had no effect\n", IR, PC.Word-1);
		Exception = TRAP_NOEFFECT;
	}
	InstructionsExecuted++;
	if (InterruptRequest && IFF1)
		ProcessIRQ();
	return Exception;
}

// Return contents of the named register pair
word GetRegister(regSpec Reg) {
	switch (Reg) {
	case REG_PC: return PC.Word;
	case REG_SP: return SP.Word;
	case REG_AF: return AF.Word;
	case REG_BC: return BC.Word;
	case REG_DE: return DE.Word;
	case REG_HL: return HL.Word;
	case REG_IX: return IX.Word;
	case REG_IY: return IY.Word;
		break;
	default:
		return 0;
		break;
	}
}

byte GetMemoryByte(word Address) {
	return Memory[Address];
}

word GetMemoryWord(word Address) {
	return Memory[Address] | (Memory[Address + 1] << 8);
}

unsigned long GetFrame() {
	return InstructionsExecuted;
}

void RaiseIRQ() {
	InterruptRequest = TRUE;
}
