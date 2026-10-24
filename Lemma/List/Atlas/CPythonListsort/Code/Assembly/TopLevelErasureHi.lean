import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.TopLevelErasureHi
open CPythonListsort


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiErase_bind_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureHi.lean)
-/
@[path]
private lemma mergeHiErase_bind_reachable
  {α β : Type*}
  (traced : TraceResult α) (raw : Option α)
  (nextTraced : α → TraceResult β) (next : α → Option β)
  (hsource : traced.erase = raw)
  (hnext : ∀ value, raw = some value →
    (nextTraced value).erase = next value) :
  (traced.bind nextTraced).erase = raw.bind next := by
  rw [TraceResult.erase_bind, hsource]
  cases hraw : raw with
  | none => simp
  | some value => simpa [hraw] using hnext value hraw

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiLoopTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureHi.lean)
-/
@[path]
lemma erase_mergeHiLoopTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {cursor : MergeHiCursor κ ν} :
-- imply
  (mergeHiLoopTraced? fuel cursor).erase = mergeHiLoop? fuel cursor := by
-- proof
  induction fuel generalizing cursor with
  | zero =>
    simp only [mergeHiLoopTraced?, mergeHiLoop?]
    by_cases hTerminal : cursor.na = 0 ∨ cursor.nb = 0
    · rw [if_pos hTerminal, if_pos hTerminal, erase_mergeHiSucceedTraced]
    · rw [if_neg hTerminal, if_neg hTerminal]
      by_cases hCopyA : cursor.nb = 1
      · rw [if_pos hCopyA, if_pos hCopyA, erase_mergeHiCopyATraced]
      · rw [if_neg hCopyA, if_neg hCopyA,
        erase_mergeHiFuelExhaustedTraced]
  | succ fuel ih =>
    simp only [mergeHiLoopTraced?, mergeHiLoop?]
    by_cases hTerminal : cursor.na = 0 ∨ cursor.nb = 0
    · rw [if_pos hTerminal, if_pos hTerminal, erase_mergeHiSucceedTraced]
    · rw [if_neg hTerminal, if_neg hTerminal]
      by_cases hCopyA : cursor.nb = 1
      · rw [if_pos hCopyA, if_pos hCopyA, erase_mergeHiCopyATraced]
      · rw [if_neg hCopyA, if_neg hCopyA]
        cases hPhase : cursor.phase with
        | straight aCount bCount =>
          apply mergeHiErase_bind_reachable
            (TraceResult.tempPayloadRead? cursor.state.a cursor.ssb)
            (mergeHiTempRead? cursor.state.a cursor.ssb) _ _
            ((TraceResult.erase_tempPayloadRead _ _).trans
              (mergeTempRead_eq_mergeHiTempRead _ _))
          intro right _
          apply mergeHiErase_bind_reachable
            (TraceResult.sortSliceKeysRead? cursor.state.data cursor.ssa)
            (cursor.state.data.read? cursor.ssa) _ _
            (TraceResult.erase_sortSliceKeysRead _ _)
          intro left _
          by_cases hCompare :
            iflt cursor.state.key_compare right.key left.key = true
          · simp only [hCompare, if_true]
            apply mergeHiErase_bind_reachable
              (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                cursor.ssa)
              (mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa)
              _ _ (erase_mergeHiCopyDataDecrTraced _ _ _)
            intro copied _
            exact ih _
          · simp only [hCompare]
            apply mergeHiErase_bind_reachable
              (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                cursor.ssb)
              (mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb)
              _ _ (erase_mergeHiCopyTempDecrTraced _ _ _)
            intro copied _
            exact ih _
        | galloping aCount bCount =>
          exact erase_mergeHiGallopRoundTraced cursor
            (mergeHiLoopTraced? fuel) (mergeHiLoop? fuel) ih

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[erase_mergeHiTracedAllocatedTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureHi.lean)
-/
@[path]
private lemma erase_mergeHiTracedAllocatedTail (state : MergeState κ ν)
  (ssa ssb : Int) (na nb : Nat) :
  (mergeHiTracedAllocatedTail? state ssa ssb na nb).erase =
    mergeHiAllocatedTail? state ssa ssb na nb := by
  unfold mergeHiTracedAllocatedTail? mergeHiAllocatedTail?
  apply mergeHiErase_bind_reachable
    (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
      mergeHiInitialDataToTempPermit nb state 0 ssb)
    (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb state 0 ssb)
    _ _
  · exact (erase_mainToTempMemcpyTraced _ _ _ _ _ _).trans
    (mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp _ _ _ _ _ _)
  · intro copiedTemp _
    apply mergeHiErase_bind_reachable
      (mergeHiCopyDataDecrTraced? copiedTemp
        (ssb + Int.ofNat (nb - 1)) (ssa + Int.ofNat (na - 1)))
      (mergeHiCopyDataDecr? copiedTemp
        (ssb + Int.ofNat (nb - 1)) (ssa + Int.ofNat (na - 1)))
      _ _ (erase_mergeHiCopyDataDecrTraced _ _ _)
    intro copied _
    exact erase_mergeHiLoopTraced (na + nb) _

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureHi.lean)
-/
@[path]
lemma erase_mergeHiTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat} :
-- imply
  (mergeHiTraced? state ssa ssb na nb).erase = mergeHi? state ssa ssb na nb := by
-- proof
  by_cases hInput :
    0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb
  · let allocated := mergeGetmem state (BitVec.ofNat 64 nb)
    have htraced :
      mergeHiTraced? state ssa ssb na nb =
        match allocated.outcome with
        | .guardRejected =>
          TraceResult.pure
            { state := allocated.state
              returnCode := -1
              fuelExhausted := false }
        | .reused | .grown =>
          mergeHiTracedAllocatedTail? allocated.state ssa ssb na nb := by
      rw [mergeHiTraced?, if_pos hInput]
      rfl
    have hraw :
      mergeHi? state ssa ssb na nb =
        match allocated.outcome with
        | .guardRejected =>
          some
            { state := allocated.state
              returnCode := -1
              fuelExhausted := false }
        | .reused | .grown =>
          mergeHiAllocatedTail? allocated.state ssa ssb na nb := by
      rw [mergeHi?, if_pos hInput]
      rfl
    rw [htraced, hraw]
    cases allocated.outcome with
    | guardRejected => rfl
    | reused => exact erase_mergeHiTracedAllocatedTail _ _ _ _ _
    | grown => exact erase_mergeHiTracedAllocatedTail _ _ _ _ _
  · rw [mergeHiTraced?, mergeHi?, if_neg hInput, if_neg hInput]
    rfl

end CPythonListsort


-- created on 2026-10-23
