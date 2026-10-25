import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.FoundNewRunSafety.Part2
import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety.Part2
import Def.CPythonListsort.Code.Assembly.TopLevelErasureHi


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[topLevelErase_bind_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasure.lean)
-/
@[path]
private lemma topLevelErase_bind_reachable
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
[erase_mergeLoLoopTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasure.lean)
-/
@[path]
lemma erase_mergeLoLoopTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {machine : MergeLoMachine κ ν}
  {phase : MergeLoPhase} :
-- imply
  (mergeLoLoopTraced? fuel machine phase).erase = mergeLoLoop? fuel machine phase := by
-- proof
  induction fuel generalizing machine phase with
  | zero => cases phase <;> rfl
  | succ fuel ih =>
    cases phase with
    | ordinary aCount bCount =>
      simp only [mergeLoLoopTraced?, mergeLoLoop?]
      split
      · rfl
      · apply topLevelErase_bind_reachable
        (TraceResult.tempPayloadRead? machine.state.a
          (Int.ofNat machine.aPos))
        (mergeLoTempRead? machine.state.a machine.aPos)
        _ _ ((TraceResult.erase_tempPayloadRead _ _).trans
          (mergeTempRead_ofNat _ _))
        intro firstA _
        apply topLevelErase_bind_reachable
          (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos)
          (machine.state.data.read? machine.bPos)
          _ _ (TraceResult.erase_sortSliceKeysRead _ _)
        intro firstB _
        by_cases hcompare :
          iflt machine.state.key_compare firstB.key firstA.key = true
        · simp only [hcompare, if_true]
          apply topLevelErase_bind_reachable
            (mergeLoCopyBIncrTraced? machine)
            (mergeLoCopyBIncr? machine)
            _ _ (erase_mergeLoCopyBIncrTraced machine)
          intro nextMachine _
          by_cases hfinished : nextMachine.nb = 0
          · simp only [hfinished, if_true]
            exact erase_mergeLoSucceedTraced _
          · simp only [hfinished, if_false]
            by_cases hthreshold :
              mergeLoCountAtLeastWord (bCount + 1)
                nextMachine.minGallop = true
            · simp only [hthreshold, if_true]
              exact ih _ _
            · simp only [hthreshold]
              exact ih _ _
        · simp only [hcompare]
          apply topLevelErase_bind_reachable
            (mergeLoCopyAIncrTraced? machine)
            (mergeLoCopyAIncr? machine)
            _ _ (erase_mergeLoCopyAIncrTraced machine)
          intro nextMachine _
          by_cases hfinished : nextMachine.na = 1
          · simp only [hfinished, if_true]
            exact erase_mergeLoCopyBTraced _
          · simp only [hfinished, if_false]
            by_cases hthreshold :
              mergeLoCountAtLeastWord (aCount + 1)
                nextMachine.minGallop = true
            · simp only [hthreshold, if_true]
              exact ih _ _
            · simp only [hthreshold]
              exact ih _ _
    | galloping =>
      simp only [mergeLoLoopTraced?, mergeLoLoop?]
      apply erase_mergeLoGallopRoundTraced
      intro nextMachine aCount bCount
      split <;> exact ih _ _

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasure.lean)
-/
@[path]
lemma erase_mergeLoTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat} :
-- imply
  (mergeLoTraced? state ssa ssb na nb).erase = mergeLo? state ssa ssb na nb := by
-- proof
  unfold mergeLoTraced? mergeLo?
  split
  · by_cases hguard :
    (mergeGetmem state (BitVec.ofNat 64 na)).outcome = .guardRejected
    · simp only [hguard, if_true]
      rfl
    · simp only [hguard, if_false]
      apply topLevelErase_bind_reachable
        (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
          mergeLoInitialDataToTempPermit na
          (mergeGetmem state (BitVec.ofNat 64 na)).state 0 ssa)
        (mergeLoMemcpyDataToTemp? .initialDataToTemp rfl na
          (mergeGetmem state (BitVec.ofNat 64 na)).state 0 ssa)
        _ _ (erase_mergeLoInitialDataToTempTraced na
          (mergeGetmem state (BitVec.ofNat 64 na)).state 0 ssa)
      intro copied _
      let machine : MergeLoMachine κ ν :=
        { state := copied
          dest := ssa
          aPos := 0
          bPos := ssb
          na := na
          nb := nb
          minGallop := copied.min_gallop }
      apply topLevelErase_bind_reachable
        (mergeLoCopyBIncrTraced? machine)
        (mergeLoCopyBIncr? machine)
        _ _ (erase_mergeLoCopyBIncrTraced machine)
      intro nextMachine _
      by_cases hfinishedB : nextMachine.nb = 0
      · simp only [hfinishedB, if_true]
        exact erase_mergeLoSucceedTraced _
      · simp only [hfinishedB, if_false]
        by_cases hfinishedA : nextMachine.na = 1
        · simp only [hfinishedA, if_true]
          exact erase_mergeLoCopyBTraced _
        · simp only [hfinishedA, if_false]
          exact erase_mergeLoLoopTraced _ _ _
  · rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_finishMergeAtPreparationTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasure.lean)
-/
@[path]
lemma erase_finishMergeAtPreparationTraced
  {κ : Type u}
  {ν : Type v}
  {prepared : MergeAtPreparation κ ν} :
-- imply
  (finishMergeAtPreparationTraced? prepared).erase = finishMergeAtPreparation? prepared := by
-- proof
  cases prepared with
  | finished result => rfl
  | mergeLo call =>
    unfold finishMergeAtPreparation?
    simp only [finishMergeAtPreparationTraced?, TraceResult.erase_map,
      TraceResult.erase_recordSuccessMemoryEvent, erase_mergeLoTraced]
    cases mergeLo? call.state call.ssa call.ssb call.na call.nb <;> rfl
  | mergeHi call =>
    unfold finishMergeAtPreparation?
    simp only [finishMergeAtPreparationTraced?, TraceResult.erase_map,
      TraceResult.erase_recordSuccessMemoryEvent, erase_mergeHiTraced]
    cases mergeHi? call.state call.ssa call.ssb call.na call.nb <;> rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeAtTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasure.lean)
-/
@[path]
lemma erase_mergeAtTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {i : Nat} :
-- imply
  (mergeAtTraced? state i).erase = mergeAt? state i := by
-- proof
  unfold mergeAtTraced? mergeAt?
  rw [TraceResult.erase_bind, erase_prepareMergeAtTraced]
  cases hprepared : prepareMergeAt? state i with
  | none => simp
  | some prepared =>
    simp only [Option.bind_some,
      mergeAt_bindOptionAcross_some]
    exact erase_finishMergeAtPreparationTraced prepared

end CPythonListsort


-- created on 2026-10-23
