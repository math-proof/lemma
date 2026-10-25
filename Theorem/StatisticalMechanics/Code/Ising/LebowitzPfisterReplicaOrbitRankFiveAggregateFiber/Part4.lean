/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u =
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
        G sites i j q u := by
  classical
  unfold lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
  apply Finset.Subset.antisymm
  · intro z hz
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    have hsplit := lpReplicaOffdiagDecoratedSource_rank_five_active_card
      G sites hsite hij q hcard z
    dsimp only at hsplit
    rcases hsplit with hthree | hsat
    · have hCnonempty : (Finset.univ \ K).Nonempty := by
        have hCcard : (Finset.univ \ K).card = 2 := by
          simpa only [K, d] using hthree.2.1
        exact Finset.card_pos.mp (by omega)
      obtain ⟨c, hc⟩ := hCnonempty
      by_cases hrow : (d.1 c).1 = false
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        exact ⟨hz, by
          change K.card = 3 /\ exists c, c ∈ Finset.univ \ K /\
            (d.1 c).1 = false
          exact ⟨hthree.1, c, hc, hrow⟩⟩
      · have hrow' : (d.1 c).1 = true := by
          cases h : (d.1 c).1 <;> simp_all
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨hz, Or.inr (by
          change K.card = 3 /\ exists c, c ∈ Finset.univ \ K /\
            (d.1 c).1 = true
          exact ⟨hthree.1, c, hc, hrow'⟩)⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨hz, Or.inl hsat⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · exact (Finset.mem_filter.mp hz).1


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u).card ≤ 4 := by
  classical
  rw [lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high
    G sites hsite hij q hcard u]
  unfold lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
  calc
    _ ≤ (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
          G sites i j q u).card +
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
          G sites i j q u).card := Finset.card_union_le _ _
    _ ≤ 3 + 1 := Nat.add_le_add
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
        G sites hsite hij q hcard u)
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one
        G sites hsite hij q hcard u)
    _ = 4 := rfl

end
end StatMech.Ising
