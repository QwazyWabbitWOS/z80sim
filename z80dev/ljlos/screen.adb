M:screen
F:G$ScreenClear$0$0({2}DF,SV:S),Z,0,2,0,0,0
S:LScreenClear$Paper$1$1({1}SC:S),B,1,4
S:LScreenClear$Ink$1$1({1}SC:S),B,1,5
S:LScreenClear$i$1$1({2}SI:S),B,1,-2
F:G$SetAttrib$0$0({2}DF,SV:S),Z,0,0,0,0,0
S:LSetAttrib$Attrib$1$1({1}SC:S),B,1,4
S:LSetAttrib$Row$1$1({1}SC:S),B,1,5
S:LSetAttrib$Column$1$1({1}SC:S),B,1,6
F:G$PutCharacter$0$0({2}DF,SV:S),Z,0,5,0,0,0
S:LPutCharacter$AsciiCode$1$1({1}SC:S),B,1,4
S:LPutCharacter$Row$1$1({1}SC:S),B,1,5
S:LPutCharacter$Column$1$1({1}SC:S),B,1,6
S:LPutCharacter$i$1$1({1}SC:S),B,1,-1
S:LPutCharacter$SectionStart$1$1({2}SI:U),B,1,-3
S:LPutCharacter$CharStart$1$1({2}SI:U),B,1,-5
S:LPutCharacter$SectionOffset$1$1({1}SC:S),R,0,0,[c]
F:G$PutString$0$0({2}DF,SV:S),Z,0,1,0,0,0
S:LPutString$String$1$1({2}DG,SC:S),B,1,4
S:LPutString$Row$1$1({1}SC:S),B,1,6
S:LPutString$Column$1$1({1}SC:S),B,1,7
S:LPutString$i$1$1({1}SC:S),R,0,0,[b]
S:LPutString$Length$1$1({1}SC:S),B,1,-1
T:Fscreen$__00010000[({0}S:S$StackFrameTop$0$0({2}DG,SV:S),Z,0,0)({2}S:S$StackFrameBottom$0$0({2}DG,SV:S),Z,0,0)({4}S:S$SP$0$0({2}DG,SI:S),Z,0,0)({6}S:S$RegisteredEvents$0$0({2}SI:S),Z,0,0)({8}S:S$EventId$0$0({1}SC:S),Z,0,0)]
S:G$SystemLock$0$0({1}SC:U),E,0,0
S:G$StringLength$0$0({2}DF,SI:S),C,0,0
S:G$StringWrite$0$0({2}DF,SV:S),C,0,0
S:G$SameString$0$0({2}DF,SC:S),C,0,0
S:G$IntToString$0$0({2}DF,SV:S),C,0,0
S:G$WordToString$0$0({2}DF,SV:S),C,0,0
S:G$WordToHex$0$0({2}DF,SV:S),C,0,0
S:G$LocksInit$0$0({2}DF,SV:S),C,0,0
S:G$LockCreate$0$0({2}DF,SC:U),C,0,0
S:G$LockObtain$0$0({2}DF,SV:S),C,0,0
S:G$LockRelease$0$0({2}DF,SV:S),C,0,0
S:G$LockQuery$0$0({2}DF,SC:S),C,0,0
S:G$SchedulingInit$0$0({2}DF,SV:S),C,0,0
S:G$SetScheduler$0$0({2}DF,SV:S),C,0,0
S:G$Scheduler$0$0({2}DF,SV:S),C,0,0
S:G$DefaultScheduler$0$0({2}DF,SV:S),C,0,0
S:G$NullScheduler$0$0({2}DF,SV:S),C,0,0
S:G$CreateTask$0$0({2}DF,DG,ST__00010000:S),C,0,0
S:G$ScheduleTask$0$0({2}DF,SV:S),C,0,0
S:G$Switch$0$0({2}DF,SV:S),C,0,0
S:G$BroadcastEvent$0$0({2}DF,SV:S),C,0,0
S:G$AwaitEvent$0$0({2}DF,SC:S),C,0,0
S:G$SupervisorMode$0$0({2}DF,SV:S),C,0,0
S:G$UserMode$0$0({2}DF,SV:S),C,0,0
S:G$Pause$0$0({2}DF,SV:S),C,0,0
S:G$Resume$0$0({2}DF,SV:S),C,0,0
S:G$IsMultitasking$0$0({2}DF,SC:S),C,0,0
S:G$ExchangeRegs$0$0({2}DF,SV:S),C,0,0
S:G$Break$0$0({2}DF,SV:S),C,0,0
S:G$Halt$0$0({2}DF,SV:S),C,0,0
S:G$SystemMonitor$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimTerminate$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimPrintCharacter$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimPrintString$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimPrintWord$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimEnterProfile$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimExitProfile$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimWriteProtect$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimReadProtect$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimRWProtect$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimUnprotect$0$0({2}DF,SV:S),C,0,0
S:G$_Z80SimWriteProtectCode$0$0({2}DF,SV:S),C,0,0
S:Fscreen$_Z80SimProtectedCodeBegins$0$0({2}DF,SV:S),C,0,0
S:Fscreen$_Z80SimProtectedCodeEnds$0$0({2}DF,SV:S),C,0,0