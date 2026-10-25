/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CenterMarkedPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
open Finset Matrix
open scoped BigOperators


namespace StatMech.Ising

theorem sum_snoc_reindex
    {E R : Type*} [Fintype E] [DecidableEq E] [AddCommMonoid R]
    (m : Nat) (F : (Fin (m + 1) -> E) -> R) :
    (∑ t, F t) = ∑ y : E × (Fin m -> E), F (Fin.snoc y.2 y.1) := by
  exact (Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 1) => E) F).symm

theorem sum_comm_three_last
    {E₁ E₂ E₃ R : Type*} [Fintype E₁] [Fintype E₂] [Fintype E₃]
    [AddCommMonoid R] (F : E₁ -> E₂ -> E₃ -> R) :
    (∑ x, ∑ y, ∑ z, F x y z) = ∑ z, ∑ x, ∑ y, F x y z := by
  calc
    (∑ x, ∑ y, ∑ z, F x y z) = ∑ x, ∑ z, ∑ y, F x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ z, ∑ x, ∑ y, F x y z := by rw [Finset.sum_comm]

end StatMech.Ising
