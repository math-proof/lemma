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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateSelectedSeamHall_iff_capacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaAggregateSelectedSeamHall G sites hsite q <->
      LPReplicaAggregateSelectedSeamCapacity G sites hsite q := by
  classical
  let f := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
  let g := fun y : LPReplicaAggregateDecoratedTarget G sites q => y.2.1
  have hequal := Fintype.hall_equalFiber_iff_card_fibers f g
  constructor
  · intro hHall
    apply hequal.mp
    intro S
    have hS := hHall S
    have hneighbors : S.biUnion
        (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q) =
        Finset.univ.filter fun y =>
          ∃ z, z ∈ S ∧ f z = g y := by
      ext y
      simp only [lpReplicaAggregateSelectedSeamNeighbors,
        LPReplicaAggregateSelectedSeamRelated, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and, f, g]
    rwa [hneighbors] at hS
  · intro hcapacity
    have hfiber : forall k : I,
        Fintype.card {z : LPReplicaAggregateDecoratedSource G sites q //
          f z = k} <=
        Fintype.card {y : LPReplicaAggregateDecoratedTarget G sites q //
          g y = k} := by
      simpa only [LPReplicaAggregateSelectedSeamCapacity, f, g] using hcapacity
    have hHall := hequal.mpr hfiber
    intro S
    have hS := hHall S
    have hneighbors : S.biUnion
        (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q) =
        Finset.univ.filter fun y =>
          ∃ z, z ∈ S ∧ f z = g y := by
      ext y
      simp only [lpReplicaAggregateSelectedSeamNeighbors,
        LPReplicaAggregateSelectedSeamRelated, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and, f, g]
    rwa [hneighbors]


theorem lpReplicaAggregateSelectedSeamRelated_connected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hrelated : LPReplicaAggregateSelectedSeamRelated
      G sites hsite q z y) :
    LPReplicaAggregateConnectedSeamRelated G sites q z y := by
  unfold LPReplicaAggregateSelectedSeamRelated at hrelated
  unfold LPReplicaAggregateConnectedSeamRelated
  rw [← hrelated]
  exact lpReplicaAggregateDecoratedSourceSelectedSeam_connected
    G sites hsite q z


theorem lpReplicaAggregateConnectedSeamHall_of_selectedSeamHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaAggregateSelectedSeamHall G sites hsite q) :
    LPReplicaAggregateConnectedSeamHall G sites q := by
  classical
  intro S
  calc
    S.card <= (S.biUnion
        (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q)).card :=
      hHall S
    _ <= (S.biUnion
        (lpReplicaAggregateConnectedSeamNeighbors G sites q)).card := by
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_biUnion] at hy ⊢
      obtain ⟨z, hz, hyz⟩ := hy
      refine ⟨z, hz, ?_⟩
      simp only [lpReplicaAggregateSelectedSeamNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and] at hyz
      simp only [lpReplicaAggregateConnectedSeamNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact lpReplicaAggregateSelectedSeamRelated_connected
        G sites hsite q z y hyz


theorem lpReplicaAggregateDecoratedInjection_of_selectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcapacity : LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
    LPReplicaAggregateDecoratedInjection G sites q := by
  classical
  have hHall := (lpReplicaAggregateSelectedSeamHall_iff_capacity
    G sites hsite q).mpr hcapacity
  have hHall' : forall S : Finset
      (LPReplicaAggregateDecoratedSource G sites q),
      S.card <= (S.biUnion
        (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q)).card := by
    simpa only [LPReplicaAggregateSelectedSeamHall] using hHall
  obtain ⟨move, hmove, _⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q)).mp hHall'
  exact ⟨move, hmove⟩


theorem lpReplicaAggregateProfileOrbitInequality_of_selectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcapacity : ∀ q,
      LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  exact lpReplicaAggregateDecoratedInjection_of_selectedSeamCapacity
    G sites hsite q (hcapacity q)


theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_selectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcapacity : ∀ q,
      LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
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
    lpReplicaAggregateProfileOrbitInequality_of_selectedSeamCapacity
      G sites hsite beta J hf r hbeta hJ hhf hr hcapacity
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
