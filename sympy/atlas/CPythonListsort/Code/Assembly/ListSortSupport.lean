/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.ListSortInputMode
import sympy.atlas.CPythonListsort.Code.Assembly.ReverseSliceSafety
import sympy.atlas.CPythonListsort.Code.Equivalence.MinrunResults
import sympy.atlas.CPythonListsort.Code.Policy.PushRunPreservation

/-!
# Support lemmas for top-level listsort assembly

This module packages the initialized `MergeState`, the adaptive-minrun state
carried by the scan, and the frame facts for the small top-level transitions.
It deliberately does not define a second listsort evaluator: the traced
top-level assembly consumes the public helpers from the reviewed
`ListSortImpl` transcription.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Selected-platform word facts -/

/-- A source-admitted list length is represented exactly by the selected
64-bit word model. -/
theorem listSizeWord_toNat {size : Nat} (hsize : size ≤ PY_LIST_MAX) :
    (BitVec.ofNat 64 size : PySSize).toNat = size := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
  omega

/-! ## Initial state -/

/-- Facts established by `initialMergeState` on a source-admitted raw input.
The explicit `hasValues` equation is retained separately from the entrywise
mode invariant because that invariant is vacuous for an empty slice. -/
structure InitialMergeStatePackage
    (lt : BoolComparator κ) (hasKeyfunc : Bool) (input : SortSlice κ ν)
    (state : MergeState κ ν) : Prop where
  exactState : state = (initialMergeState lt hasKeyfunc input).1
  listlenRoundtrip : state.listlen.toNat = input.entries.size
  listlenNonnegative : state.listlen.Nonnegative
  basekeys : state.basekeys = 0
  data : state.data = input
  pending : state.pending = #[]
  pendingLayout : PendingLayout state 0
  poweredPrefix : PoweredPrefix state
  tempInvariant : TempStorageInv state.a state.alloced
  tempLive : state.a.Live
  logicalCapacity : state.a.cells.size = state.alloced.toNat
  physicalSlotsBound :
    state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES
  hasValues : state.a.hasValues = hasKeyfunc
  valuesMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data
  comparator : state.key_compare = lt
  minrunState : state.minrunState = minrunInit state.listlen
  minrunStopped : (initialMergeState lt hasKeyfunc input).2 = true

/-- State carried between scan iterations. `emittedLeScanned` records that
every already-emitted minrun target was covered by the actual runs consumed so
far; natural runs may make the inequality strict. -/
structure AdaptiveMinrunScanInvariant
    (listSize : PySSize) (calls scanned : Nat) (state : MinrunState) : Prop where
  listNonnegative : listSize.Nonnegative
  listMax : listSize.toNat ≤ PY_LIST_MAX
  stateEq : state = (minrunNextN calls (minrunInit listSize)).state
  emittedLeScanned :
    (minrunNextN calls (minrunInit listSize)).outputs.sum ≤ scanned
  scannedBound : scanned ≤ listSize.toNat

/-- Facts about the next adaptive target on an active valid scan. -/
structure AdaptiveMinrunStepFacts
    (listSize : PySSize) (calls scanned : Nat) (state : MinrunState) : Prop where
  assertionPassed : (minrunNext state).assertionPassed = true
  targetPositive : 1 ≤ (minrunNext state).result.toNat
  targetMax : (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat
  nextState :
    (minrunNext state).state =
      (minrunNextN (calls + 1) (minrunInit listSize)).state
  emittedOutputs :
    (minrunNextN (calls + 1) (minrunInit listSize)).outputs =
      (minrunNextN calls (minrunInit listSize)).outputs ++
        [(minrunNext state).result.toNat]

/-! ## Final-reversal phase selection -/

/-- CPython's final reverse acts on saved values in keyed mode and on the key
array itself in unkeyed mode. -/
def finalReversePhase (hasValues : Bool) : ReverseSlicePhase :=
  if hasValues then .values else .keys
