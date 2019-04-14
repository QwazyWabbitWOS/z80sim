#ifndef H_DEBUG
#define H_DEBUG

#include "types.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

logic Debugger(void);
void InitDebugger(void);
logic BreakRequest();
void ReadFileLine(FILE* Handle, unsigned int Line, char* String);

#endif
