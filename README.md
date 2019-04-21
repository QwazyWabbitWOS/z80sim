z80sim
======

A simulator and debugger for the Z80 processor.

This fork enhances the 'step' function in the debugger
and adds Visual Studio 2017 project files.
Some logic errors are fixed and the formatting of
code is aligned to a more standard style for debugging
purposes.
Style changes were made to eliminate potential undefined behavior.
The help display is a bit more explanatory.

The emulator is still fairly imcomplete. Some primary opcodes are not implemented and a lot of the multi-byte opcodes are not implemented. 

Progess is being made on the disassembler. The only undecoded instructions are the DDCB and FDCB groups.
