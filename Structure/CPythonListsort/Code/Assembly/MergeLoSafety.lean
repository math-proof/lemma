/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Assembly.MergeLoSafety
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

/-! ## Public safety vocabulary -/

/-- State fields that `merge_lo` is not allowed to mutate.  `min_gallop` is
intentionally absent; it is the merge's adaptive output. -/
structure MergeLoStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeLoStableFrame

/-- Exact temporary-storage metadata preserved after `merge_getmem` has
selected the backing used by `merge_lo`.  Payload cells may change during the
initial main-to-temporary copy, so this frame deliberately records their
extent rather than their contents. -/
structure MergeLoStorageFrame (before after : MergeState κ ν) : Prop where
  cellsSize : after.a.cells.size = before.a.cells.size
  backing : after.a.backing = before.a.backing
  hasValues : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced

namespace MergeLoStorageFrame

/-- Inductive invariant for every live left-to-right merge machine.  The three
cursor equalities are the exact arithmetic preserved by cell and block moves. -/
structure MergeLoMachineInvariant (origin : MergeState κ ν)
    (tempTotal : Nat) (endIndex : Int) (machine : MergeLoMachine κ ν) : Prop where
  destNonnegative : 0 ≤ machine.dest
  tempAccounting : machine.aPos + machine.na = tempTotal
  adjacency : machine.dest + Int.ofNat machine.na = machine.bPos
  rightAccounting : machine.bPos + Int.ofNat machine.nb = endIndex
  mainEnd : endIndex ≤ Int.ofNat machine.state.data.entries.size
  leftWordBound : machine.na ≤ PY_LIST_MAX
  rightWordBound : machine.nb ≤ PY_LIST_MAX
  tempCapacity : tempTotal ≤ machine.state.a.cells.size
  tempValuesMode : TempRangeValuesMode machine.state.a 0 tempTotal
  tempInvariant : TempStorageInv machine.state.a machine.state.alloced
  tempLive : machine.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant machine.state.a.hasValues machine.state.data
  stableFrame : MergeLoStableFrame origin machine.state
  storageFrame : MergeLoStorageFrame origin machine.state

end MergeLoStorageFrame
end MergeLoStableFrame
end CPythonListsort
