/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
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

namespace MergeHiStableFrame

namespace MergeHiStorageFrame

namespace MergeHiCursorInvariant

/-- Evidence produced by the call-site/allocation stage.  It fixes the exact
initial `memcpy`, the forced first backward copy, and the cursor invariant that
the recursive phase machine consumes. -/
structure MergeHiPrepared
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (forced : MergeHiDataCursorResult κ ν) : Prop where
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.nb call
  geometry : MergeAtSafetyGeometry pre scanned i call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  directionalDispatch : call.nb < call.na
  allocation : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
  initialCopy : MainToTempMemcpyPost (.hi .initialDataToTemp)
    mergeHiInitialDataToTempPermit call.nb (mergeHiAllocated call).state copied
    0 call.ssb
  forcedResult :
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1))).result = some forced
  forcedSafe : MovementTraceSafe
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1)))
  initialInvariant : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
    (mergeHiInitialCursor call forced)
  initialFuel : MergeHiFuelInvariant (call.na + call.nb)
    (mergeHiInitialCursor call forced)

/-- Lockstep result after the recursive merge driver has finished.  Besides
the aggregate core contract, this stage retains the exact traced entry shape
and the non-vacuous temporary-read witness needed by the observable post. -/
structure MergeHiLockstepPost
    (call : MergeAtCall κ ν) (copied : MergeState κ ν)
    (result : MergeHiResult κ ν) : Prop where
  core : MergeHiCorePost (mergeHiAllocated call).state call.nb
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
    (mergeHi? call.state call.ssa call.ssb call.na call.nb) result
  tracedEntry :
    mergeHiTraced? call.state call.ssa call.ssb call.na call.nb =
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb).bind
          (mergeHiTracedAfterCopy call)
  afterCopyRead :
    (mergeHiTracedAfterCopy call copied).trace.HasTempAccess .read

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
