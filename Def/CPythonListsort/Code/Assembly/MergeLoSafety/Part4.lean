/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety.Part3
/-!
# `merge_lo` lockstep safety

This module instruments the reviewed `merge_lo` transcription with the typed
main-data and temporary-storage primitives from `MergeTracePrimitives`.
Temporary gallops read their actual temporary backing directly; the
materialized `SortSlice` is used only as an untraced semantic bridge to the
reviewed evaluator.
-/


namespace CPythonListsort

universe u v w

variable {κ : Type u} {ν : Type v}

namespace MergeLoStableFrame

namespace MergeLoStorageFrame

namespace MergeLoMachineInvariant

/-! ## Staged public-proof assembly -/

/-- Initial machine installed after the left run has been copied to temporary
storage. -/
def mergeLoInitialMachine (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : MergeLoMachine κ ν :=
  { state := state
    dest := call.ssa
    aPos := 0
    bPos := call.ssb
    na := call.na
    nb := call.nb
    minGallop := state.min_gallop }

/-- Exclusive end of the right input run, fixed throughout `merge_lo`. -/
def mergeLoEndIndex (call : MergeAtCall κ ν) : Int :=
  call.ssb + Int.ofNat call.nb

/-- The post-initial-move traced continuation. -/
def mergeLoTracedTail (call : MergeAtCall κ ν)
    (machine : MergeLoMachine κ ν) : TraceResult (MergeLoResult κ ν) :=
  if machine.nb = 0 then
    mergeLoSucceedTraced? machine
  else if machine.na = 1 then
    mergeLoCopyBTraced? machine
  else
    mergeLoLoopTraced? (call.na + call.nb + 1) machine (.ordinary 0 0)

/-- Erased counterpart of `mergeLoTracedTail`. -/
def mergeLoReferenceTail (call : MergeAtCall κ ν)
    (machine : MergeLoMachine κ ν) : Option (MergeLoResult κ ν) :=
  if machine.nb = 0 then
    mergeLoSucceed? machine
  else if machine.na = 1 then
    mergeLoCopyB? machine
  else
    mergeLoLoop? (call.na + call.nb + 1) machine (.ordinary 0 0)

/-- The full continuation after the initial main-to-temporary bulk copy. -/
def mergeLoTracedAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : TraceResult (MergeLoResult κ ν) :=
  (mergeLoCopyBIncrTraced? (mergeLoInitialMachine call state)).bind
    (mergeLoTracedTail call)

/-- Erased counterpart of `mergeLoTracedAfterCopy`. -/
def mergeLoReferenceAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : Option (MergeLoResult κ ν) :=
  (mergeLoCopyBIncr? (mergeLoInitialMachine call state)).bind
    (mergeLoReferenceTail call)

end MergeLoMachineInvariant
end MergeLoStorageFrame
end MergeLoStableFrame
end CPythonListsort
