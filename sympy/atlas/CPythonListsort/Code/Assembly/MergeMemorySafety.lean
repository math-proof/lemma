/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.ListSortTermination

/-!
# Aggregate temporary merge-memory safety

This module is the public projection of the literal merge-memory history
carried by `listSortImplTraced?`.  It does not define another evaluator or a
separately supplied history: every lifecycle field below refers directly to
the `memoryEvents` stored in the actual top-level execution trace.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Complete temporary-memory certificate for the raw top-level evaluator.

The two public premises of `listSortImpl_mergeMemory_safe` are deliberately
not stored here: this postcondition records only observable execution facts
and the representation facts proved for the returned state. -/
structure ListSortImplMergeMemorySafetyPost
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (result : ListSortImplResult κ ν) : Prop where
  /-- The actual traced evaluator returns this result. -/
  resultEq :
    (listSortImplTraced? lt reverse hasKeyfunc input).result = some result
  /-- The modeled C return code is successful. -/
  returnCode : result.returnCode = 0
  /-- The returned result does not report fuel exhaustion. -/
  resultFuel : result.fuelExhausted = false
  /-- The actual trace does not report fuel exhaustion. -/
  traceFuel :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.fuelExhausted =
      false
  /-- Erasing the trace recovers the unchanged raw evaluator. -/
  exactErasure :
    (listSortImplTraced? lt reverse hasKeyfunc input).erase =
      listSortImpl? lt reverse hasKeyfunc input
  /-- The unchanged raw evaluator itself returns the same successful result. -/
  rawResultEq : listSortImpl? lt reverse hasKeyfunc input = some result
  /-- Every recorded array access is inside its recorded extent. -/
  allAccessesInBounds :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.allAccessesInBounds
  /-- No temporary payload access occurs while backing is released. -/
  tempPayloadAccessesLive :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.tempPayloadAccessesLive
  /-- Every physically recorded post-push stack depth is at most 61. -/
  stackDepthMax :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.stackDepthMax ≤ 61
  /-- The proved depth is strictly below CPython's pending-stack capacity. -/
  stackDepthBelowCapacity : 61 < MAX_MERGE_PENDING
  /-- The concrete storage installed by `merge_init` already satisfies the
  selected-platform physical pointer-slot ceiling. -/
  initialPhysicalBound :
    (MergeMemorySnapshot.ofState
      (initialMergeState lt hasKeyfunc input).1).PhysicalBound
  /-- The actual trace is exactly initializer, continuous directional calls,
  and terminal cleanup, at the concrete state snapshots shown here. -/
  memoryLifecycle :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.MergeMemoryLifecycle
      hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt hasKeyfunc input).1)
      (MergeMemorySnapshot.ofState result.state)
  /-- Cleanup preserves the temporary-storage representation invariant. -/
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  /-- The final main array still agrees with the retained values mode. -/
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  /-- The retained mode bit is exactly the mode established by initialization. -/
  finalHasValues : result.state.a.hasValues = hasKeyfunc
  /-- The final concrete allocation observation remains within the selected
  platform's physical pointer-slot bound. -/
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound
  /-- Every merge `memcpy` callsite crosses distinct temporary/main backing;
  same-backing bulk movement is routed through `memmove`. -/
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν

/-- Complete temporary-memory certificate at the validated public boundary. -/
structure ListSortMergeMemorySafetyPost
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (result : ListSortImplResult κ ν) : Prop where
  /-- The actual validated-input traced evaluator returns this result. -/
  resultEq : (listSortTraced? lt reverse input).result = some result
  /-- The modeled C return code is successful. -/
  returnCode : result.returnCode = 0
  /-- The returned result does not report fuel exhaustion. -/
  resultFuel : result.fuelExhausted = false
  /-- The actual trace does not report fuel exhaustion. -/
  traceFuel : (listSortTraced? lt reverse input).trace.fuelExhausted = false
  /-- Erasing the trace recovers the unchanged public evaluator. -/
  exactErasure :
    (listSortTraced? lt reverse input).erase = listSort? lt reverse input
  /-- The unchanged public evaluator itself returns the same successful result. -/
  rawResultEq : listSort? lt reverse input = some result
  /-- Every recorded array access is inside its recorded extent. -/
  allAccessesInBounds :
    (listSortTraced? lt reverse input).trace.allAccessesInBounds
  /-- No temporary payload access occurs while backing is released. -/
  tempPayloadAccessesLive :
    (listSortTraced? lt reverse input).trace.tempPayloadAccessesLive
  /-- Every physically recorded post-push stack depth is at most 61. -/
  stackDepthMax :
    (listSortTraced? lt reverse input).trace.stackDepthMax ≤ 61
  /-- The proved depth is strictly below CPython's pending-stack capacity. -/
  stackDepthBelowCapacity : 61 < MAX_MERGE_PENDING
  /-- The concrete storage installed by `merge_init` already satisfies the
  selected-platform physical pointer-slot ceiling. -/
  initialPhysicalBound :
    (MergeMemorySnapshot.ofState
      (initialMergeState lt input.hasKeyfunc input.slice).1).PhysicalBound
  /-- The actual trace is exactly initializer, continuous directional calls,
  and terminal cleanup, at the concrete state snapshots shown here. -/
  memoryLifecycle :
    (listSortTraced? lt reverse input).trace.MergeMemoryLifecycle
      input.hasKeyfunc
      (MergeMemorySnapshot.ofState
        (initialMergeState lt input.hasKeyfunc input.slice).1)
      (MergeMemorySnapshot.ofState result.state)
  /-- Cleanup preserves the temporary-storage representation invariant. -/
  finalTempInvariant : TempStorageInv result.state.a result.state.alloced
  /-- The final main array still agrees with the retained values mode. -/
  finalValuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  /-- The retained mode bit is exactly the validated input mode. -/
  finalHasValues : result.state.a.hasValues = input.hasKeyfunc
  /-- The final concrete allocation observation remains within the selected
  platform's physical pointer-slot bound. -/
  finalPhysicalBound :
    (MergeMemorySnapshot.ofState result.state).PhysicalBound
  /-- The closed merge bulk-copy inventory satisfies callsite provenance. -/
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν

/-- Concrete total Boolean comparator used only by the executable witnesses. -/
def natLt (left right : Nat) : Bool := decide (left < right)

/-- Empty ordinary-array input with a fixed payload universe. -/
def emptyUnkeyed : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs #[]

/-- Empty keyed input; its mode bit remains observable even though the
entrywise values-mode invariant is vacuous. -/
def emptyKeyed : ListSortInput Nat Nat :=
  ListSortInput.keyed #[]

/-- Two increasing natural runs whose boundary descends, so the top-level
scan discovers two distinct runs before final collapse. -/
def twoRunKeys (leftLength rightLength : Nat) : Array Nat :=
  (Array.range leftLength |>.map fun key => 1000 + key) ++
    Array.range rightLength

/-- Equal 33-element runs force the left-to-right merge direction. -/
def loInput : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs (twoRunKeys 33 33)

/-- A 33-element left run and 32-element right run force the right-to-left
merge direction. -/
def hiInput : ListSortInput Nat Unit :=
  ListSortInput.unkeyedAs (twoRunKeys 33 32)

/-- Observable directional-call projection of the literal top-level trace. -/
def directions {payload : Type} (input : ListSortInput Nat payload) :
    List MergeMemoryDirection :=
  (listSortTraced? natLt false input).trace.memoryEvents.filterMap fun
    | .mergeCall call => some call.direction
    | _ => none

/-- One increasing keyed run used by the repeated-growth fixture. -/
def keyedRun (base length : Nat) : Array (Nat × Nat) :=
  (Array.range length).map fun offset =>
    let key := base + offset
    (key, key)

/-- Four descending-by-block 129-element keyed runs.  The first pair grows
past keyed inline capacity 128; the final 258/258 merge then frees that heap
buffer and grows again. -/
def releasedGrowthInput : ListSortInput Nat Nat :=
  ListSortInput.keyed
    (keyedRun 3000 129 ++ keyedRun 2000 129 ++
      keyedRun 1000 129 ++ keyedRun 0 129)

/-- For every actual directional call, retain the optional freed backing,
the post-`merge_getmem` backing, and its logical cell count. -/
def growthSummaries :
    List (Option TempBacking × TempBacking × Nat) :=
  (listSortTraced? natLt false releasedGrowthInput).trace.memoryEvents.filterMap
    fun
      | .mergeCall call =>
          some (call.intermediateFree.map (·.backing),
            call.afterGetmem.backing, call.afterGetmem.cellsSize)
      | _ => none

end MergeMemoryRegression
