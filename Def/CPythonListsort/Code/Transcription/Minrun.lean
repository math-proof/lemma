/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Minrun.lean -/

import Def.CPythonListsort.Code.Transcription.Word
import Structure.CPythonListsort.Code.Transcription.Minrun
/-!
# Adaptive-minrun transcription

Sources: `Objects/listobject.c`, lines 2230-2268 (`merge_init`) and
2745-2754 (`minrun_next`) at CPython commit
`67e6be72be9c0b75a31795ed42f9afb5eb431d47`.
-/


namespace CPythonListsort

/--
The loop
`while (list_size >> mr_e >= MAX_MINRUN) { ++mr_e; }`, with explicit fuel.
-/
def minrunExponentLoop : Nat → PySSize → Nat → Nat × Bool
  | 0, _, exponent => (exponent, false)
  | fuel + 1, listSize, exponent =>
      if (listSize.sshiftRight exponent).slt MAX_MINRUN then
        (exponent, true)
      else
        minrunExponentLoop fuel listSize (exponent + 1)

/-- The adaptive-minrun portion of CPython's `merge_init`, with loop status. -/
def minrunInitTraced (listSize : PySSize) : MinrunInitTrace :=
  let exponentResult := minrunExponentLoop 64 listSize 0
  let exponent : PySSize := BitVec.ofNat 64 exponentResult.1
  { state :=
      { listlen := listSize
        mr_current := 0
        mr_e := exponent
        -- C's unsuffixed literal makes this an `int` expression; the selected
        -- platform fixes `int` at 32 bits and records that bit pattern here.
        mr_mask := ((((1 : BitVec 32) <<< exponentResult.1) - 1).zeroExtend 64) }
    stopped := exponentResult.2 }

/-- The adaptive-minrun fields produced by the transcribed `merge_init` fragment. -/
def minrunInit (listSize : PySSize) : MinrunState :=
  (minrunInitTraced listSize).state

end CPythonListsort
