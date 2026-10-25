/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem nonempty_lpReplicaAggregatePooledMatching_iff_hall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaAggregatePooledMatching G sites hsite q) <->
      LPReplicaAggregatePooledHall G sites hsite q := by
  classical
  constructor
  · rintro ⟨m⟩
    unfold LPReplicaAggregatePooledHall
    apply (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaAggregatePooledNeighbors G sites hsite q)).mpr
    refine ⟨m.output, m.output_injective, ?_⟩
    intro z
    simp only [lpReplicaAggregatePooledNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact m.output_related z
  · intro hHall
    have hHall' : forall S : Finset
        (LPReplicaAggregateDecoratedSource G sites q),
        S.card <= (S.biUnion
          (lpReplicaAggregatePooledNeighbors G sites hsite q)).card := by
      simpa only [LPReplicaAggregatePooledHall] using hHall
    obtain ⟨move, hmove, hmem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (lpReplicaAggregatePooledNeighbors G sites hsite q)).mp hHall'
    refine ⟨{
      output := move
      output_injective := hmove
      output_related := ?_
    }⟩
    intro z
    have hz := hmem z
    simpa only [lpReplicaAggregatePooledNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and] using hz


theorem lpReplicaAggregateDecoratedInjection_of_pooledMatching
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m : LPReplicaAggregatePooledMatching G sites hsite q) :
    LPReplicaAggregateDecoratedInjection G sites q :=
  ⟨m.output, m.output_injective⟩


theorem lpReplicaAggregateProfileOrbitInequality_of_aggregatePooledHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hHall : ∀ q, LPReplicaAggregatePooledHall G sites hsite q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  have hm :=
    (nonempty_lpReplicaAggregatePooledMatching_iff_hall
      G sites hsite q).mpr (hHall q)
  exact lpReplicaAggregateDecoratedInjection_of_pooledMatching
    G sites hsite q (Classical.choice hm)


theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_aggregatePooledHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hHall : ∀ q, LPReplicaAggregatePooledHall G sites hsite q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    (∑ i : I, ∑ j : I,
      lpMatchingFiveCurrentCoefficient H beta Jr
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  have horbit :=
    lpReplicaAggregateProfileOrbitInequality_of_aggregatePooledHall
      G sites hsite beta J hf r hbeta hJ hhf hr hHall
  have hmatch := lpReplicaMatchingDisconn_le_of_profileOrbit
    G sites beta J hf r hbeta hJ hhf hr horbit
  dsimp only at hmatch
  apply (lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])).mpr
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn H beta Jr
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  exact hmatch


end
end StatMech.Ising
