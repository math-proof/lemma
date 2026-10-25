/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_le_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    (lpReplicaOffdiagRankFiveOutputCollisionClassLow
      G sites i j q output y).card ≤ 3 := by
  classical
  let u := lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y
  have hsub : lpReplicaOffdiagRankFiveOutputCollisionClassLow
      G sites i j q output y ⊆
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
        G sites i j q u := by
    intro z hz
    simp only [lpReplicaOffdiagRankFiveOutputCollisionClassLow,
      lpReplicaOffdiagRankFiveOutputCollisionClass,
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive,
      Finset.mem_filter] at hz ⊢
    exact ⟨hz.1.1, hz.2⟩
  exact (Finset.card_le_card hsub).trans
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
      G sites hsite hij q hcard u)


theorem lpReplicaOffdiagRankFiveOutputCollisionClassHigh_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    (lpReplicaOffdiagRankFiveOutputCollisionClassHigh
      G sites i j q output y).card ≤ 1 := by
  classical
  let u := lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y
  have hsub : lpReplicaOffdiagRankFiveOutputCollisionClassHigh
      G sites i j q output y ⊆
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
        G sites i j q u := by
    intro z hz
    simp only [lpReplicaOffdiagRankFiveOutputCollisionClassHigh,
      lpReplicaOffdiagRankFiveOutputCollisionClass,
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive,
      Finset.mem_filter] at hz ⊢
    exact ⟨hz.1.1, hz.2⟩
  exact (Finset.card_le_card hsub).trans
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one
      G sites hsite hij q hcard u)

set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagRankFiveOutputCollisionClass_eq_low_union_high
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : by
      classical
      exact lpReplicaOffdiagRankFiveOutputCollisionClass
          G sites i j q output y =
        (lpReplicaOffdiagRankFiveOutputCollisionClassLow
          G sites i j q output y)
          ∪ (lpReplicaOffdiagRankFiveOutputCollisionClassHigh
            G sites i j q output y) := by
  classical
  let u := lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y
  have hsplit :=
    lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high
      G sites hsite hij q hcard u
  ext z
  constructor
  · intro hz
    have hz' := Finset.mem_filter.mp hz
    have hzSplit : z ∈
        lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
          G sites i j q u := by
      rw [← hsplit]
      exact hz'.1
    rcases Finset.mem_union.mp hzSplit with hzLow | hzHigh
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hz, (Finset.mem_filter.mp hzLow).2⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hz, (Finset.mem_filter.mp hzHigh).2⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · exact (Finset.mem_filter.mp hz).1


theorem
    lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_ge_two_of_three_le
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
    (hthree : 3 ≤ (lpReplicaOffdiagRankFiveOutputCollisionClass
      G sites i j q output y).card) :
    2 ≤ (lpReplicaOffdiagRankFiveOutputCollisionClassLow
      G sites i j q output y).card := by
  classical
  have hunion :=
    lpReplicaOffdiagRankFiveOutputCollisionClass_eq_low_union_high
      G sites hsite hij q hcard output y
  have hle : (lpReplicaOffdiagRankFiveOutputCollisionClass
      G sites i j q output y).card ≤
      (lpReplicaOffdiagRankFiveOutputCollisionClassLow
          G sites i j q output y).card +
        (lpReplicaOffdiagRankFiveOutputCollisionClassHigh
          G sites i j q output y).card := by
    rw [hunion]
    exact Finset.card_union_le
      (lpReplicaOffdiagRankFiveOutputCollisionClassLow
        G sites i j q output y)
      (lpReplicaOffdiagRankFiveOutputCollisionClassHigh
        G sites i j q output y)
  have hhigh :=
    lpReplicaOffdiagRankFiveOutputCollisionClassHigh_card_le_one
      G sites hsite hij q hcard output y
  omega

end
end StatMech.Ising
