-- Generated from the frozen masked-memory LLBC by project_stateful.py.
import BulksketchBridge.X86MaskedMemoryLlbcRuntime

namespace BulksketchBridge.X86MaskedMemory.Llbc

def loadProgram : List Op := [
  .live 0, -- LLBC 0
  .live 2, -- LLBC 1
  .live 3, -- LLBC 2
  .live 4, -- LLBC 3
  .reborrow 4 1 false, -- LLBC 4
  .len 3 4, -- LLBC 7
  .dead 4, -- LLBC 8
  .mask 2 3, -- LLBC 11
  .dead 3, -- LLBC 12
  .live 5, -- LLBC 13
  .live 6, -- LLBC 14
  .live 7, -- LLBC 15
  .reborrow 7 1 false, -- LLBC 16
  .asPtr 6 7 false, -- LLBC 19
  .dead 7, -- LLBC 20
  .cast 5 6 false, -- LLBC 23
  .dead 6, -- LLBC 24
  .load 0 2 5, -- LLBC 27
  .dead 5, -- LLBC 28
  .dead 2, -- LLBC 29
  .dead 1, -- LLBC 30
  .ret] -- LLBC 31

def storeProgram : List Op := [
  .live 0, -- LLBC 32
  .initUnit 0, -- LLBC 33
  .live 3, -- LLBC 34
  .live 4, -- LLBC 35
  .live 5, -- LLBC 36
  .reborrow 5 1 true, -- LLBC 37
  .asPtr 4 5 true, -- LLBC 41
  .dead 5, -- LLBC 42
  .cast 3 4 true, -- LLBC 46
  .dead 4, -- LLBC 47
  .live 6, -- LLBC 48
  .live 7, -- LLBC 49
  .live 8, -- LLBC 50
  .reborrow 8 1 false, -- LLBC 51
  .len 7 8, -- LLBC 55
  .dead 8, -- LLBC 56
  .mask 6 7, -- LLBC 60
  .dead 7, -- LLBC 61
  .live 9, -- LLBC 62
  .copyRegister 9 2, -- LLBC 63
  .store 0 3 6 9, -- LLBC 67
  .dead 9, -- LLBC 68
  .dead 6, -- LLBC 69
  .dead 3, -- LLBC 70
  .dead 2, -- LLBC 71
  .dead 1, -- LLBC 72
  .ret] -- LLBC 73

end BulksketchBridge.X86MaskedMemory.Llbc
