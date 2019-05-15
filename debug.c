#include "debug.h"

#include "cpu.h"
#include "tokens.h"
#include "watch.h"
#include "parser.h"
#include "sizes.h"
#include "symbols.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define CMD_INFO     1
#define CMD_RUN      2
#define CMD_STEP     3
#define CMD_STEPI    4
#define CMD_WATCH    5
#define CMD_EVAL     6
#define CMD_DISASM   7
#define CMD_STACK    8
#define CMD_IRQ      9
#define CMD_NAME    10
#define CMD_QUIT    11
#define CMD_ENABLE  12
#define CMD_DISABLE 13
#define CMD_HELP    14
#define CMD_RESET   15
#define CMD_EXAMINE 16
#define CMD_TRACE   17

#define CMD_INFO_WATCHPOINTS 100
#define CMD_INFO_WARRANTY    101

#define LEX_QUIT             "quit"
#define LEX_HELP             "help"
#define LEX_INFO             "info"
#define LEX_RUN              "run"
#define LEX_STEP             "step"
#define LEX_STEPI            "stepi"
#define LEX_TRACE            "trace"
#define LEX_WATCH            "watch"
#define LEX_EVAL             "eval"
#define LEX_DISASM           "disasm"
#define LEX_EXAMINE          "exam"
#define LEX_STACK            "stack"
#define LEX_IRQ              "irq"
#define LEX_NAME             "name"
#define LEX_ENABLE           "enable"
#define LEX_DISABLE          "disable"
#define LEX_RESET            "reset"
#define LEX_INFO_WATCHPOINTS "watchpoints"
#define LEX_INFO_WARRANTY    "warranty"

static tokens* DebugTokens;

static logic StopAtNextCLine = FALSE;

void PrintValue(FILE* Handle, word Value) {
	if (Value > 9) fprintf(Handle, "0x%04x", Value);
	else fprintf(Handle, "%d", Value);
}

void Input(const char* Prompt, char* UserString) {
	fprintf(stdout, "%s", Prompt);
	fflush(stdout);
	fgets(UserString, MAX_STRING, stdin);
	UserString[strlen(UserString) - 1] = '\0';
}

void InitDebugger(void) {
	InitParser();
	InitWatchpoints();
	DebugTokens = CreateTokenTable();
	CreateToken(DebugTokens, " ", 0);
	// Debugger commands
	CreateToken(DebugTokens, LEX_QUIT, CMD_QUIT);
	CreateToken(DebugTokens, LEX_HELP, CMD_HELP);
	CreateToken(DebugTokens, LEX_INFO, CMD_INFO);
	CreateToken(DebugTokens, LEX_RUN, CMD_RUN);
	CreateToken(DebugTokens, LEX_STEP, CMD_STEP);
	CreateToken(DebugTokens, LEX_STEPI, CMD_STEPI);
	CreateToken(DebugTokens, LEX_WATCH, CMD_WATCH);
	CreateToken(DebugTokens, LEX_EVAL, CMD_EVAL);
	CreateToken(DebugTokens, LEX_DISASM, CMD_DISASM);
	CreateToken(DebugTokens, LEX_EXAMINE, CMD_EXAMINE);
	CreateToken(DebugTokens, LEX_STACK, CMD_STACK);
	CreateToken(DebugTokens, LEX_TRACE, CMD_TRACE);
	CreateToken(DebugTokens, LEX_IRQ, CMD_IRQ);
	CreateToken(DebugTokens, LEX_NAME, CMD_NAME);
	CreateToken(DebugTokens, LEX_ENABLE, CMD_ENABLE);
	CreateToken(DebugTokens, LEX_DISABLE, CMD_DISABLE);
	CreateToken(DebugTokens, LEX_RESET, CMD_RESET);
	// Command parameters
	CreateToken(DebugTokens, LEX_INFO_WATCHPOINTS, CMD_INFO_WATCHPOINTS);
	CreateToken(DebugTokens, LEX_INFO_WARRANTY, CMD_INFO_WARRANTY);
}

logic BreakRequest(void)
{
	static logic OldLineSkipped = FALSE;
	if (StopAtNextCLine) {
		if (OldLineSkipped && HasSource(GetRegister(REG_PC)))
		{
			StopAtNextCLine = FALSE;
			OldLineSkipped = FALSE;
			return TRUE;
		}
		else OldLineSkipped = TRUE;
	}
	if (CheckWatchpoints() != NULL) return TRUE;
	return FALSE;
}

void ExecuteInfoWarranty() {
	fprintf(stdout, "                            NO WARRANTY\n\n");
	fprintf(stdout, "  11. BECAUSE THE PROGRAM IS LICENSED FREE OF CHARGE, THERE IS NO WARRANTY\n");
	fprintf(stdout, "FOR THE PROGRAM, TO THE EXTENT PERMITTED BY APPLICABLE LAW.  EXCEPT WHEN\n");
	fprintf(stdout, "OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER PARTIES\n");
	fprintf(stdout, "PROVIDE THE PROGRAM \"AS IS\" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESSED\n");
	fprintf(stdout, "OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF\n");
	fprintf(stdout, "MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.  THE ENTIRE RISK AS\n");
	fprintf(stdout, "TO THE QUALITY AND PERFORMANCE OF THE PROGRAM IS WITH YOU.  SHOULD THE\n");
	fprintf(stdout, "PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF ALL NECESSARY SERVICING,\n");
	fprintf(stdout, "REPAIR OR CORRECTION.\n");
	fprintf(stdout, "  12. IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING\n");
	fprintf(stdout, "WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MAY MODIFY AND/OR\n");
	fprintf(stdout, "REDISTRIBUTE THE PROGRAM AS PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES,\n");
	fprintf(stdout, "INCLUDING ANY GENERAL, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING\n");
	fprintf(stdout, "OUT OF THE USE OR INABILITY TO USE THE PROGRAM (INCLUDING BUT NOT LIMITED\n");
	fprintf(stdout, "TO LOSS OF DATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY\n");
	fprintf(stdout, "YOU OR THIRD PARTIES OR A FAILURE OF THE PROGRAM TO OPERATE WITH ANY OTHER\n");
	fprintf(stdout, "PROGRAMS), EVEN IF SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE\n");
	fprintf(stdout, "POSSIBILITY OF SUCH DAMAGES.\n");
}

void ExecuteInfo(const char* Parameters) {
	char Lexeme[MAX_STRING];
	int Token;
	const char* OtherSymbols = Parameters;
	while ((Token = ExtractToken(DebugTokens, &OtherSymbols, Lexeme, TRUE)) == 0) {
		if (strlen(Lexeme) == 0) {
			fprintf(stdout, "Info on what?\n");
			fprintf(stdout, "watchpoints, warranty are supported\n");
			return;
		}
	}
	switch (Token) {
	case CMD_INFO_WATCHPOINTS:
		ListWatchpoints(stdout);
		break;
	case CMD_INFO_WARRANTY:
		ExecuteInfoWarranty();
		break;
	default:
		fprintf(stdout, "No info about '%s'\n", Lexeme);
	}
}

void ExecuteWatch(const char* Parameters) {
	operation* Watchpoint;
	Watchpoint = ParseExpression(Parameters);
	if (Watchpoint == NULL) {
		fprintf(stdout, "A parse error in expression.\n");
	}
	else {
		char Expression[MAX_STRING];
		StringifyExpression(Watchpoint, Expression);
		fprintf(stdout, "Watchpoint %d: %s (currently 0x%04x)\n",
			AddWatchpoint(Watchpoint, TRUE), Expression, EvaluateExpression(Watchpoint));
	}
}

void ExecuteEval(const char* Parameters) {
	operation* Representation;
	Representation = ParseExpression(Parameters);
	if (Representation == NULL) {
		fprintf(stdout, "A parse error in expression.\n");
	}
	else {
		char Expression[MAX_STRING];
		StringifyExpression(Representation, Expression);
		fprintf(stdout, "%s evaluates to ", Expression);
		PrintValue(stdout, EvaluateExpression(Representation));
		fprintf(stdout, "\n");
		FreeExpression(Representation);
	}
}

// Disassemble from Start to End, end address optional.
void ExecuteDisasm(const char* Parameters) {
	word Start = 0;
	word End = 0;
	char StartStr[MAX_STRING] = "";
	char EndStr[MAX_STRING] = "";
	const char* OtherTokens = Parameters;
	if (!ExtractFreeform(DebugTokens, &OtherTokens, StartStr))
	{
		fprintf(stdout, "Syntax: disasm start-addr <end-addr>\n");
		return;
	}
	else {
		ExtractFreeform(DebugTokens, &OtherTokens, EndStr);
		Start = (word)strtoul(StartStr, NULL, 0);
		End = (word)strtoul(EndStr, NULL, 0);
		word i;
		if (End <= Start)
			End = Start + 1;
		i = Start;
		while (i <= End && i != 0xffff)
		{
			char Mnemonic[MAX_STRING];
			fprintf(stdout, "%04x: ", i);
			Disassemble(&i, Mnemonic);
			fprintf(stdout, "%s\n", Mnemonic);
		}
	}
}

// Examine memory from Start to End, end address optional.
void ExecuteExamine(const char* Parameters) {
	word Start = 0;
	word End = 0;
	char StartStr[MAX_STRING] = "";
	char EndStr[MAX_STRING] = "";
	const char* OtherTokens = Parameters;
	if (!ExtractFreeform(DebugTokens, &OtherTokens, StartStr))
	{
		fprintf(stdout, "Syntax: "LEX_EXAMINE" start-addr <end-addr>\n");
		return;
	}
	else {
		ExtractFreeform(DebugTokens, &OtherTokens, EndStr);
		Start = (word)strtoul(StartStr, NULL, 0);
		End = (word)strtoul(EndStr, NULL, 0);
		if (End <= Start)
			End = Start;
		word i = Start;
		while (i <= End && i != 0xffff)
		{
			fprintf(stdout, "%04x: ", i);
			fprintf(stdout, "%02x\n", GetMemoryByte(i++));
		}
	}
}

void ExecuteStack(const char* Parameters) {
	char DepthStr[MAX_NAME];
	word Start, End;
	word i;
	Start = GetRegister(REG_SP);
	if (!ExtractFreeform(DebugTokens, &Parameters, DepthStr))
		End = Start + 3;
	else
		End = Start + (word)strtol(DepthStr, NULL, 0);
	fprintf(stdout, "%04x: %04x  <- SP\n", Start, GetMemoryWord(Start));
	for (i = Start + 1; i < End; i += 2) {
		fprintf(stdout, "%04x: %04x\n", i, GetMemoryWord(i));
	}
}

void ExecuteName(const char* Parameters) {
	char AddrStr[MAX_STRING];
	char Symbol[MAX_NAME];
	if (!ExtractFreeform(DebugTokens, &Parameters, AddrStr)) {
		fprintf(stdout, "Syntax: name <addr>\n");
	}
	else {
		word Addr = (word)strtol(AddrStr, NULL, 0);
		if (LookupSymbol(Addr, Symbol)) {
			fprintf(stdout, "Symbol: '%s'\n", Symbol);
		}
		else if (SearchSymbol(Addr, Symbol)) {
			fprintf(stdout, "Nearest symbol: '%s'\n", Symbol);
		}
		else fprintf(stdout, "No symbol found\n");
	}
}

void ExecuteEnable(const char* Parameters) {
	char NumberStr[MAX_STRING];
	while (ExtractFreeform(DebugTokens, &Parameters, NumberStr)) {
		short Number = (word)strtol(NumberStr, NULL, 0);
		if (ExistsWatchpoint(Number)) {
			WatchpointActivation(Number, TRUE);
		}
		else {
			fprintf(stdout, "Watchpoint %d does not exist\n", Number);
		}
	}
}

void ExecuteDisable(const char* Parameters) {
	char NumberStr[MAX_STRING];
	while (ExtractFreeform(DebugTokens, &Parameters, NumberStr)) {
		short Number = (short)strtol(NumberStr, NULL, 0);
		if (ExistsWatchpoint(Number)) {
			WatchpointActivation(Number, FALSE);
		}
		else {
			fprintf(stdout, "Watchpoint %d does not exist\n", Number);
		}
	}
}

void ShowTrace(word Addr, char* Mnemonic)
{
	PrintRegisters(stdout);
	fprintf(stdout, "  -  %04x: ", Addr);
	Disassemble(&Addr, Mnemonic);
	fprintf(stdout, "%s\n", Mnemonic);
}

logic Debugger() {
	watchpoint* Watch;
	word InstructionAddress;
	char Mnemonic[MAX_NAME];

	while (NULL != (Watch = CheckWatchpoints())) {
		char Expression[MAX_STRING];
		StringifyExpression(Watch->Trigger, Expression);
		fprintf(stdout, "\nBREAK: %s has changed value\n", Expression);
		fprintf(stdout, "Old value: ");
		PrintValue(stdout, Watch->StableValue); fprintf(stdout, "\n");
		fprintf(stdout, "New value: ");
		PrintValue(stdout, Watch->StableValue = EvaluateExpression(Watch->Trigger));
		fprintf(stdout, "\n");

		// Dump state at the breakpoint
		InstructionAddress = GetRegister(REG_PC);
		PrintRegisters(stdout);
		fprintf(stdout, "  -  %04x: ", InstructionAddress);
		Disassemble(&InstructionAddress, Mnemonic);
		fprintf(stdout, "%s\n", Mnemonic);
	}
	{
		source SourceSpec = SearchSource(GetRegister(REG_PC));
		if (SourceSpec.File != NULL) {
			char SourceLine[MAX_STRING];
			ReadFileLine(SourceSpec.File, SourceSpec.Line, SourceLine);
			fprintf(stdout, "%d %s\n", SourceSpec.Line, SourceLine);
		}
	}
	for (;;) {
		char CommandLine[MAX_STRING];
		char Token[MAX_STRING];
		const char* OtherTokens = CommandLine;
		Input("$ ", CommandLine);
		switch (ExtractToken(DebugTokens, &OtherTokens, Token, TRUE)) {
		case CMD_QUIT:
			exit(0);
		case CMD_HELP:
			fprintf(stdout, "\t%s\t%s\n", LEX_DISABLE, "Disable watchpoint");
			fprintf(stdout, "\t%s\t%s\n", LEX_DISASM, "Disassemble ("LEX_DISASM" addr <addr>)");
			fprintf(stdout, "\t%s\t%s\n", LEX_ENABLE, "Enable a disabled watchpoint");
			fprintf(stdout, "\t%s\t%s\n", LEX_EVAL, "Evaluate expression [<expression>]");
			fprintf(stdout, "\t%s\t%s\n", LEX_EXAMINE, "Examine memory ("LEX_EXAMINE" addr <addr>)");
			fprintf(stdout, "\t%s\t%s\n", LEX_INFO, "Get info on...");
			fprintf(stdout, "\t%s\t%s\n", LEX_IRQ, "*Not implemented*");
			fprintf(stdout, "\t%s\t%s\n", LEX_NAME, "Give symbolic name of an address");
			fprintf(stdout, "\t%s\t%s\n", LEX_QUIT, "Quit the simulator");
			fprintf(stdout, "\t%s\t%s\n", LEX_RESET, "Reset the CPU");
			fprintf(stdout, "\t%s\t%s\n", LEX_RUN, "Run the simulation at speed");
			fprintf(stdout, "\t%s\t%s\n", LEX_STACK, "Display n words at stack pointer ("LEX_STACK" [n])");
			fprintf(stdout, "\t%s\t%s\n", LEX_STEP, "Single-step the next opcode");
			fprintf(stdout, "\t%s\t%s\n", LEX_STEPI, "Single-step the next C line");
			fprintf(stdout, "\t%s\t%s\n", LEX_TRACE, "Toggle console tracing");
			fprintf(stdout, "\t%s\t%s\n", LEX_WATCH, "Set watchpoint");
			fprintf(stdout, "\tinfo %s\n", LEX_INFO_WATCHPOINTS);
			fprintf(stdout, "\tinfo %s\n", LEX_INFO_WARRANTY);
			break;
		case CMD_INFO:
			ExecuteInfo(OtherTokens);
			break;
		case CMD_RUN:
			fprintf(stdout, "Resuming execution\n\n");
			return FALSE;
		case CMD_STEP:
			return TRUE;
		case CMD_STEPI:
			StopAtNextCLine = TRUE;
			return FALSE;
		case CMD_WATCH:
			ExecuteWatch(OtherTokens);
			break;
		case CMD_TRACE:
			TraceExecution = !TraceExecution;
			fprintf(stdout, "Tracing %s\n", TraceExecution ? "ON": "Off");
			break;
		case CMD_EVAL:
			ExecuteEval(OtherTokens);
			break;
		case CMD_DISASM:
			ExecuteDisasm(OtherTokens);
			break;
		case CMD_EXAMINE:
			ExecuteExamine(OtherTokens);
			break;
		case CMD_STACK:
			ExecuteStack(OtherTokens);
			break;
		case CMD_NAME:
			ExecuteName(OtherTokens);
			break;
		case CMD_ENABLE:
			ExecuteEnable(OtherTokens);
			break;
		case CMD_DISABLE:
			ExecuteDisable(OtherTokens);
			break;
		case CMD_RESET:		//power-on reset the Z80
			ResetCPU();
			break;
		default:
			fprintf(stdout, "Unknown command.\n");
		}
	}
}
