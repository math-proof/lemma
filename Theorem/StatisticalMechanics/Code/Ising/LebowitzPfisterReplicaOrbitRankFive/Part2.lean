/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFour
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitMultiplicityClass
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in

@[simp] theorem mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
        G sites i j q u ↔
      z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u ∧
        LPReplicaOffdiagDecoratedSource.IsErasedRankFive
          G sites i j q z := by
  classical
  simp [lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive]

set_option maxHeartbeats 800000 in


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_eligible
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
        G sites i j q u).card ≤
      (lpReplicaEligibleInactivePairs
        (lpReplicaOrbitFourColorSlotEdge G sites q u)).card := by
  classical
  let inactivePair := fun z : LPReplicaOffdiagDecoratedSource G sites i j q =>
    Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  apply Finset.card_le_card_of_injOn inactivePair
  · intro z hz
    simp only [Finset.mem_coe] at hz ⊢
    rw [mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive]
      at hz
    obtain ⟨c, hcC, hctag, hthree⟩ := hz.2
    have hmem :=
      lpReplicaOffdiagDecoratedSource_rank_five_inactivePair_mem_eligible
        G sites hsite hij q hcard z hthree c hcC hctag
    have htrace : lpReplicaOffdiagDecoratedSourceCrossTrace
        G sites i j q z = u := (Finset.mem_filter.mp hz.1).2
    simpa only [inactivePair, htrace] using hmem
  · intro z hz w hw hpairs
    simp only [Finset.mem_coe] at hz hw
    rw [mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive]
      at hz hw
    apply lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
      G sites i j q u hz.1 hw.1
    exact (sdiff_right_inj (Finset.subset_univ _) (Finset.subset_univ _)).mp
      hpairs


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
        G sites i j q u).card ≤ 3 := by
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_eligible
    G sites hsite hij q hcard u).trans
      (lpReplicaEligibleInactivePairs_card_le_three
        (lpReplicaOrbitFourColorSlotEdge G sites q u))


end
end StatMech.Ising
