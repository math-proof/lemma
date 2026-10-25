/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaLowRowCrossTraceOutputRowMaskTwo_val
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u)) :
    (lpReplicaLowRowCrossTraceOutputRowMaskTwo
      G sites hsite hij q hcard u z).1 =
      (lpReplicaLowRowCrossTraceOutput
        G sites hsite hij q hcard u z).1 := by
  rfl


theorem
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_of_lowOutputInjective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (hinjective : Function.Injective
      (lpReplicaLowRowCrossTraceOutput
        G sites hsite hij q hcard u)) :
    (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
      G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  classical
  let low := lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
    G sites i j q u
  let high := lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
    G sites i j q u
  let target := lpReplicaOffdiagBalancedOutputCrossTraceFiber
    G sites i j q u
  let targetTwo := lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
    G sites i j q u 2
  let targetFour := lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
    G sites i j q u 4
  let lowOutput : ↑low -> ↑targetTwo :=
    lpReplicaLowRowCrossTraceOutputRowMaskTwo
      G sites hsite hij q hcard u
  have hlowOutput : Function.Injective lowOutput := by
    intro z w hzw
    apply hinjective
    apply Subtype.ext
    rw [← lpReplicaLowRowCrossTraceOutputRowMaskTwo_val
        G sites hsite hij q hcard u z,
      ← lpReplicaLowRowCrossTraceOutputRowMaskTwo_val
        G sites hsite hij q hcard u w]
    exact congrArg Subtype.val hzw
  have hlowCard : low.card <= targetTwo.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective lowOutput hlowOutput
  have hhighCard : high.card <= targetFour.card := by
    exact lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_maskFourTarget
      G sites hsite hij q hcard u
  have hsourceDisjoint : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro z hzLow hzHigh
    have hzLow' := Finset.mem_filter.mp hzLow
    have hzHigh' := Finset.mem_filter.mp hzHigh
    have hlowMask :=
      lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
        G sites hsite hij q hcard z hzLow'.2
    have hhighMask :=
      lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
        G sites hsite hij q hcard z hzHigh'.2.1
    rw [hhighMask, Finset.card_univ, hcard] at hlowMask
    omega
  have htargetDisjoint : Disjoint targetTwo targetFour := by
    rw [Finset.disjoint_left]
    intro y hyTwo hyFour
    exact lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskTwo_disjoint_four
      G sites i j q u y ⟨hyTwo, hyFour⟩
  have htargetSubset : targetTwo ∪ targetFour ⊆ target := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyTwo | hyFour
    · exact (Finset.mem_filter.mp hyTwo).1
    · exact (Finset.mem_filter.mp hyFour).1
  rw [lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive,
    Finset.card_union_of_disjoint hsourceDisjoint]
  calc
    low.card + high.card <= targetTwo.card + targetFour.card :=
      Nat.add_le_add hlowCard hhighCard
    _ = (targetTwo ∪ targetFour).card :=
      (Finset.card_union_of_disjoint htargetDisjoint).symm
    _ <= target.card := Finset.card_le_card htargetSubset


end
end StatMech.Ising
