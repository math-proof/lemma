/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part4
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteWeightedPoissonBarrier_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) (hx : boundary x) :
    isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit x = 0 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y ↦ if boundary y then 0 else -1)) x
  change (if boundary x then
      isingFiniteWeightedPoissonBarrier G conductance boundary
        hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedPoissonBarrier G conductance boundary
          hconductance hpositive hhit) x) =
    (if boundary x then 0 else -1) at h
  simpa [hx] using h

theorem isingFiniteWeightedPoissonBarrier_laplacian
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) (hx : ¬ boundary x) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedPoissonBarrier G conductance boundary
        hconductance hpositive hhit) x = -1 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y ↦ if boundary y then 0 else -1)) x
  change (if boundary x then
      isingFiniteWeightedPoissonBarrier G conductance boundary
        hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedPoissonBarrier G conductance boundary
          hconductance hpositive hhit) x) =
    (if boundary x then 0 else -1) at h
  simpa [hx] using h

theorem isingFiniteWeightedPoissonBarrier_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    ∀ x, 0 ≤ isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit x := by
  apply isingFiniteWeighted_const_le_superharmonic
    G conductance boundary
    (isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit) 0 hconductance hpositive hhit
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_laplacian
      G conductance boundary hconductance hpositive hhit x hx]
    norm_num
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_boundary
      G conductance boundary hconductance hpositive hhit x hx]

end
end StatMech.Universality
