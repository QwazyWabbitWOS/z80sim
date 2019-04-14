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


#ifndef H_SYMBOLS
#define H_SYMBOLS

#include "types.h"
#include <stdio.h>

typedef struct {
        FILE* File;
        unsigned int Line;
} source;

void InitSymbols(void);
logic LoadSymbols(FILE* Handle);
logic SearchSymbol(word Address, char* Name);
source SearchSource(word Address);
logic HasSource(word Address);
logic LookupSymbol(word Address, char* Name);
logic ExistsSymbol(const char* Name);
word GetSymbol(const char* Name);
logic LookupSymbol(word Address, char* Name);
logic LoadSourcePointers(FILE* Handle);
logic LookupSymbol(word Address, char* Name);

#endif
