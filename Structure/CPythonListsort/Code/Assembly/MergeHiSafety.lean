/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part2
/-!
# `merge_hi` traced execution and safety

This module instruments the right-to-left merge directly.  Its evaluator does
not run `mergeHi?` and attach a second, decorative trace: every state transition
is produced by the typed operation that emits its access events.  The three
`memcpy` paths retain their exact source call-site tag and distinct-backing
permit, main-data block movement uses the overlap-safe traced `memmove`, and
temporary gallops read their live storage through `GallopKeySource.temporary`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- State fields that the merge is forbidden to change.  Allocation may
change `a`, its backing, and `alloced`; the adaptive `min_gallop` is also an
intentional merge output. -/
structure MergeHiStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeHiStableFrame

/-- Exact temporary-storage metadata preserved after `merge_getmem` has
selected the backing used by `merge_hi`.  The initial copy may replace payload
contents, so the frame records their extent rather than extensional equality. -/
structure MergeHiStorageFrame (before after : MergeState κ ν) : Prop where
  cellsSize : after.a.cells.size = before.a.cells.size
  backing : after.a.backing = before.a.backing
  hasValues : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced

namespace MergeHiStorageFrame

/-- Inductive invariant for every live right-to-left merge cursor.  The three
equalities are the subtraction-sensitive core: they retain the legal `-1`
sentinels rather than coercing backward cursors through `Nat`. -/
structure MergeHiCursorInvariant (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν) : Prop where
  baseNonnegative : 0 ≤ cursor.basea
  ssaEquation : cursor.ssa + 1 = cursor.basea + Int.ofNat cursor.na
  ssbEquation : cursor.ssb + 1 = Int.ofNat cursor.nb
  destEquation :
    cursor.dest + 1 = cursor.basea + Int.ofNat (cursor.na + cursor.nb)
  mainRange :
    cursor.basea + Int.ofNat (cursor.na + cursor.nb) ≤
      Int.ofNat cursor.state.data.entries.size
  leftWordBound : cursor.na ≤ PY_LIST_MAX
  rightWordBound : cursor.nb ≤ PY_LIST_MAX
  tempCapacity : cursor.nb ≤ cursor.state.a.cells.size
  tempValuesMode : TempRangeValuesMode cursor.state.a 0 cursor.nb
  tempInvariant : TempStorageInv cursor.state.a cursor.state.alloced
  tempLive : cursor.state.a.Live
  requestFits : request ≤ cursor.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant cursor.state.a.hasValues cursor.state.data
  stableFrame : MergeHiStableFrame origin cursor.state
  storageFrame : MergeHiStorageFrame origin cursor.state

end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
