/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part4


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem isingFiniteWeightedDirichletSolve_add
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (f g : V -> Real) :
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit (f + g) =
      isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit f +
        isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit g := by
  apply isingFiniteWeightedDirichletOperator_injective
    G conductance boundary hconductance hpositive hhit
  rw [isingFiniteWeightedDirichletOperator_solve, map_add,
    isingFiniteWeightedDirichletOperator_solve,
    isingFiniteWeightedDirichletOperator_solve]


theorem isingFiniteWeightedDirichletSolve_smul
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (c : Real) (f : V -> Real) :
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit (c • f) =
      c • isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit f := by
  apply isingFiniteWeightedDirichletOperator_injective
    G conductance boundary hconductance hpositive hhit
  rw [isingFiniteWeightedDirichletOperator_solve, map_smul,
    isingFiniteWeightedDirichletOperator_solve]


theorem isingFiniteWeightedDirichletSolve_sum
    {V I : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (s : Finset I) (f : I -> V -> Real) :
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit (∑ i ∈ s, f i) =
      ∑ i ∈ s,
        isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply isingFiniteWeightedDirichletOperator_injective
        G conductance boundary hconductance hpositive hhit
      simp [isingFiniteWeightedDirichletOperator_solve]
  | @insert a s ha ih =>
      simp only [sum_insert ha]
      rw [isingFiniteWeightedDirichletSolve_add, ih]


theorem isingFiniteWeightedLaplacian_pair_comm
    {V : Type*} [Fintype V]
    (conductance : V -> V -> Real)
    (hsymm : forall x y, conductance x y = conductance y x)
    (f g : V -> Real) :
    (∑ x, f x * isingFiniteWeightedLaplacian conductance g x) =
      ∑ x, g x * isingFiniteWeightedLaplacian conductance f x := by
  classical
  let L : Real := ∑ x, ∑ y,
    f x * conductance x y * (g y - g x)
  let R : Real := ∑ x, ∑ y,
    g x * conductance x y * (f y - f x)
  let E : Real := ∑ x, ∑ y,
    conductance x y * (f y - f x) * (g y - g x)
  have hleft :
      (∑ x, f x * isingFiniteWeightedLaplacian conductance g x) = L := by
    unfold L isingFiniteWeightedLaplacian
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hright :
      (∑ x, g x * isingFiniteWeightedLaplacian conductance f x) = R := by
    unfold R isingFiniteWeightedLaplacian
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hswapL : L = ∑ x, ∑ y,
      f y * conductance x y * (g x - g y) := by
    unfold L
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsymm]
  have hswapR : R = ∑ x, ∑ y,
      g y * conductance x y * (f x - f y) := by
    unfold R
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsymm]
  have henergyL : 2 * L = -E := by
    calc
      2 * L = L + L := by ring
      _ = L + ∑ x, ∑ y,
          f y * conductance x y * (g x - g y) := by rw [hswapL]
      _ = -E := by
        unfold L E
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y _
        ring
  have henergyR : 2 * R = -E := by
    calc
      2 * R = R + R := by ring
      _ = R + ∑ x, ∑ y,
          g y * conductance x y * (f x - f y) := by rw [hswapR]
      _ = -E := by
        unfold R E
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y _
        ring
  rw [hleft, hright]
  linarith


theorem isingFiniteGhostConductance_comm
    {V : Type*} (G : SimpleGraph V) (ghostRate : V -> Real)
    (x y : Option V) :
    isingFiniteGhostConductance G ghostRate x y =
      isingFiniteGhostConductance G ghostRate y x := by
  classical
  cases x with
  | none => cases y <;> rfl
  | some x =>
      cases y with
      | none => rfl
      | some y =>
          simp only [isingFiniteGhostConductance]
          rw [G.adj_comm]


end
end StatMech.Universality
