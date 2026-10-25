/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem isingFiniteWeightedSpatialResidualPotential_eq_sum_point
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (residual : V -> Real) :
    isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual =
      ∑ z ∈ (Finset.univ : Finset V),
        residual z • isingFiniteWeightedPointPoissonBarrier
          G conductance boundary hconductance hpositive hhit z := by
  classical
  have hrhs :
      (fun x => if boundary x then (0 : Real) else -residual x) =
        ∑ z ∈ (Finset.univ : Finset V),
          residual z •
            (fun x => if boundary x then (0 : Real) else
              if x = z then -1 else 0) := by
    funext x
    by_cases hx : boundary x
    · simp [hx]
    · simp [hx]
  unfold isingFiniteWeightedSpatialResidualPotential
    isingFiniteWeightedPointPoissonBarrier
  calc
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit
        (fun x => if boundary x then 0 else -residual x) =
      isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit
        (∑ z ∈ (Finset.univ : Finset V),
          residual z •
            (fun x => if boundary x then (0 : Real) else
              if x = z then -1 else 0)) :=
        congrArg (isingFiniteWeightedDirichletSolve
          G conductance boundary hconductance hpositive hhit) hrhs
    _ = ∑ z ∈ (Finset.univ : Finset V),
        isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit
          (residual z •
            (fun x => if boundary x then (0 : Real) else
              if x = z then -1 else 0)) :=
      isingFiniteWeightedDirichletSolve_sum G conductance boundary
        hconductance hpositive hhit _ _
    _ = ∑ z ∈ (Finset.univ : Finset V),
        residual z •
          isingFiniteWeightedDirichletSolve G conductance boundary
            hconductance hpositive hhit
            (fun x => if boundary x then (0 : Real) else
              if x = z then -1 else 0) := by
      apply Finset.sum_congr rfl
      intro z _
      exact isingFiniteWeightedDirichletSolve_smul
        G conductance boundary hconductance hpositive hhit _ _


theorem isingFiniteWeightedSpatialResidualPotential_le_sum_point_bound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (residual bound : V -> Real) (x : V)
    (hresidual : forall z, 0 <= residual z)
    (hbound : forall z,
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit z x <= bound z) :
    isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual x <=
      ∑ z ∈ (Finset.univ : Finset V), residual z * bound z := by
  rw [congrFun (isingFiniteWeightedSpatialResidualPotential_eq_sum_point
    G conductance boundary hconductance hpositive hhit residual) x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro z _
  exact mul_le_mul_of_nonneg_left (hbound z) (hresidual z)


end
end StatMech.Universality
