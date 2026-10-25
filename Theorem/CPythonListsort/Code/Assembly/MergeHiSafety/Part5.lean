/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Structure.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
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

/-- Safety of the concrete `merge_hi` continuation selected by `merge_at`.
All cursor geometry, allocation admissibility, positivity, word bounds, and
backward-sentinel arithmetic are derived from the pending layout and the
actual preparation equation. -/
theorem mergeHi_safe
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ result, MergeHiSafetyPost pre scanned i call
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result := by
  rcases mergeHi_prepare pre scanned i call hlayout hmax hprepare hInv hLive
      hMode with ⟨copied, forced, hprepared⟩
  rcases mergeHi_lockstep pre scanned i call copied forced hprepared with
    ⟨result, hlockstep⟩
  have hobservable := mergeHi_observables pre scanned i call copied forced
    result hprepared hlockstep
  have hcore := hobservable.core
  have hlogical := TempStorageInv.cells_size_eq hcore.tempInvariant
    hcore.tempLive
  have hphysicalBound :
      call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
        result.state.a.physicalSlots ≤
          PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
    intro hbefore
    rw [hcore.storageFrame.physicalSlots_eq]
    rcases hprepared.allocation.outcome with hreuse | hgrown
    · rw [hprepared.allocation.reuseAccounting hreuse]
      exact hbefore
    · exact (hprepared.allocation.growthAccounting hgrown).2.2.2.2
  exact ⟨result,
    { resultEq := hcore.resultEq
      returnCode := hcore.returnCode
      resultFuel := hcore.resultFuel
      traceFuel := hcore.traceSafe.fuel
      accessesInBounds := hcore.traceSafe.bounds
      tempAccessesLive := hcore.traceSafe.tempLive
      noPushes := hcore.traceSafe.noPushes
      noMemoryEvents := mergeHiTraced_memoryEvents_empty
        call.state call.ssa call.ssb call.na call.nb
      exactErasure := hcore.exactErasure
      tempInvariant := hcore.tempInvariant
      tempLive := hcore.tempLive
      logicalCapacity := hlogical
      requestFits := hcore.requestFits
      valuesMode := hcore.valuesMode
      stableFrame := (MergeHiStableFrame.of_getmem call.state
        (BitVec.ofNat 64 call.nb) hprepared.allocation).trans hcore.stableFrame
      geometry := hprepared.geometry
      requestFacts := hprepared.requestFacts
      inputTempInvariant := hprepared.inputTempInvariant
      inputTempLive := hprepared.inputTempLive
      inputValuesMode := hprepared.inputValuesMode
      directionalDispatch := hprepared.directionalDispatch
      allocationPost := hprepared.allocation
      postGetmemStorageFrame := hcore.storageFrame
      physicalSlotsBound := hphysicalBound
      memcpyProvenance := hobservable.memcpyProvenance
      inputKeyEvent := hobservable.inputKeyEvent
      tempWriteEvent := hobservable.tempWriteEvent
      tempReadEvent := hobservable.tempReadEvent
      synchronizedValuesEvent := hobservable.synchronizedValuesEvent }⟩

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
