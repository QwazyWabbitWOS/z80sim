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

The original emulator was very incomplete. Some primary opcodes were not implemented and many of the multi-byte opcodes were not implemented. 

This fork of the disassembler now decodes all instructions and optionally uses Zilog mnemonics vs sdcc mnemonics.
Improved trace log output.
