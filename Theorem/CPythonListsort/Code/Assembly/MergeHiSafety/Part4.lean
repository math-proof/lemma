/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Structure.CPythonListsort.Code.Assembly.MergeHiSafety.Part4
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

/-- The loop/lockstep stage consumes only the prepared cursor contract.  It
proves termination, exact erasure against the untraced transcription, and a
real temporary read on every successful path. -/
theorem mergeHi_lockstep
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (forced : MergeHiDataCursorResult κ ν)
    (hprepared : MergeHiPrepared pre scanned i call copied forced) :
    ∃ result, MergeHiLockstepPost call copied result := by
  have hgeometry := hprepared.geometry
  have hallocPost := hprepared.allocation
  have hcopy := hprepared.initialCopy
  have hinitial := hprepared.initialInvariant
  rcases mergeHiLoopTraced_safe (mergeHiAllocated call).state call.nb
      (call.na + call.nb)
      (mergeHiInitialCursor call forced) hinitial hprepared.initialFuel with
    ⟨result, hloop⟩
  have hsumPositive : 0 < call.na + call.nb := by
    have hna := hgeometry.leftPositive
    omega
  let loopFuel := call.na + call.nb - 1
  have hloopFuelEq : call.na + call.nb = loopFuel + 1 := by
    dsimp [loopFuel]
    omega
  have hloopRead :
      (mergeHiLoopTraced? (call.na + call.nb)
        (mergeHiInitialCursor call forced)).trace.HasTempAccess .read := by
    by_cases hnaZero : (mergeHiInitialCursor call forced).na = 0
    · have hnbPositive : 0 < (mergeHiInitialCursor call forced).nb := by
        simpa [mergeHiInitialCursor] using hgeometry.rightPositive
      rw [hloopFuelEq]
      simpa [mergeHiLoopTraced?, hnaZero] using
        mergeHiSucceedTraced_hasTempRead (mergeHiAllocated call).state call.nb
          (mergeHiInitialCursor call forced) hinitial hnbPositive
    · have hnaPositive : 0 < (mergeHiInitialCursor call forced).na :=
        Nat.pos_of_ne_zero hnaZero
      by_cases hnbOne : (mergeHiInitialCursor call forced).nb = 1
      · have hterminal : ¬ ((mergeHiInitialCursor call forced).na = 0 ∨
            (mergeHiInitialCursor call forced).nb = 0) := by
          omega
        rw [hloopFuelEq, mergeHiLoopTraced?, if_neg hterminal,
          if_pos hnbOne]
        exact mergeHiCopyATraced_hasTempRead (mergeHiAllocated call).state call.nb
          (mergeHiInitialCursor call forced) hinitial ⟨hnbOne, hnaPositive⟩
      · have hnbLarge : 1 < (mergeHiInitialCursor call forced).nb := by
          have hnbPositive : 0 < (mergeHiInitialCursor call forced).nb := by
            simpa [mergeHiInitialCursor] using hgeometry.rightPositive
          omega
        rw [hloopFuelEq]
        exact mergeHiInitialLoop_hasTempRead loopFuel
          (mergeHiInitialCursor call forced) hnaPositive hnbLarge (by rfl)
  have hloop' : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTracedTail call forced) (mergeHiReferenceTail call forced)
      result := by
    simpa [mergeHiTracedTail, mergeHiReferenceTail] using hloop
  have hafterForced := MergeHiCorePost.prepend
    (mergeHiAllocated call).state call.nb
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1)))
    (mergeHiTracedTail call) (mergeHiReferenceTail call) forced result
    hprepared.forcedResult hprepared.forcedSafe hloop'
  have hafterCopy : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTracedAfterCopy call copied)
      (mergeHiReferenceAfterCopy call copied) result := by
    simpa [mergeHiTracedAfterCopy, mergeHiReferenceAfterCopy,
      erase_mergeHiCopyDataDecrTraced] using hafterForced
  have hafterCopyRead :
      (mergeHiTracedAfterCopy call copied).trace.HasTempAccess .read := by
    apply mergeHiHasTempAccess_bind_right
      (mergeHiCopyDataDecrTraced? copied
        (call.ssb + Int.ofNat (call.nb - 1))
        (call.ssa + Int.ofNat (call.na - 1)))
      (mergeHiTracedTail call) forced .read hprepared.forcedResult
    simpa [mergeHiTracedTail] using hloopRead
  have hwhole := MergeHiCorePost.prepend (mergeHiAllocated call).state call.nb
    (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
      mergeHiInitialDataToTempPermit call.nb
      (mergeHiAllocated call).state 0 call.ssb)
    (mergeHiTracedAfterCopy call) (mergeHiReferenceAfterCopy call) copied
    result hcopy.success hcopy.traceSafe hafterCopy
  have hreference :
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
          mergeHiInitialDataToTempPermit call.nb
          (mergeHiAllocated call).state 0 call.ssb).erase.bind
            (mergeHiReferenceAfterCopy call) =
        (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiReferenceAfterCopy call) := by
    calc
      _ = (mainToTempMemcpy? call.nb (mergeHiAllocated call).state 0
          call.ssb).bind (mergeHiReferenceAfterCopy call) := congrArg
            (fun option => option.bind (mergeHiReferenceAfterCopy call))
            hcopy.exactErasure
      _ = _ := congrArg
        (fun option => option.bind (mergeHiReferenceAfterCopy call))
        (mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp .initialDataToTemp rfl
          call.nb (mergeHiAllocated call).state 0 call.ssb)
  have hwholeTagged := MergeHiCorePost.reference_eq hwhole hreference
  have hentryGuard :
      0 < call.na ∧ 0 < call.nb ∧ call.na ≤ PY_SSIZE_T_MAX ∧
        call.nb ≤ PY_SSIZE_T_MAX ∧
        call.ssa + Int.ofNat call.na = call.ssb :=
    ⟨hgeometry.leftPositive, hgeometry.rightPositive,
      hgeometry.leftWordBound, hgeometry.rightWordBound, hgeometry.adjacent⟩
  have htracedEntry :
      mergeHiTraced? call.state call.ssa call.ssb call.na call.nb =
        (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
          mergeHiInitialDataToTempPermit call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiTracedAfterCopy call) := by
    rw [mergeHiTraced?, if_pos hentryGuard]
    change (match (mergeHiAllocated call).outcome with
      | .guardRejected => _
      | .reused => _
      | .grown => _) = _
    rcases hallocPost.outcome with houtcome | houtcome
    · rw [houtcome]
      rfl
    · rw [houtcome]
      rfl
  have hreferenceEntry :
      mergeHi? call.state call.ssa call.ssb call.na call.nb =
        (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiReferenceAfterCopy call) := by
    rw [mergeHi?, if_pos hentryGuard]
    change (match (mergeHiAllocated call).outcome with
      | .guardRejected => _
      | .reused => _
      | .grown => _) = _
    rcases hallocPost.outcome with houtcome | houtcome
    · rw [houtcome]
      rfl
    · rw [houtcome]
      rfl
  have hcore : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
      (mergeHi? call.state call.ssa call.ssb call.na call.nb) result := by
    rw [htracedEntry, hreferenceEntry]
    exact hwholeTagged
  exact ⟨result,
    { core := hcore
      tracedEntry := htracedEntry
      afterCopyRead := hafterCopyRead }⟩

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort
