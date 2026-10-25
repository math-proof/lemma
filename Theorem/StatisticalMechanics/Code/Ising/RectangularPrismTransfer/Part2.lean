/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Def.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part2
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

theorem sum_rectangularPrismSite_eq
    {m n h : Nat} (f : RectangularPrismSite m n h -> Real) :
    (∑ v, f v) = ∑ x : Fin m, ∑ y : Fin n,
      ∑ z : Fin (2 * h + 1), f ⟨x, y, z⟩ := by
  calc
    (∑ v, f v) = ∑ p : Fin m × Fin n × Fin (2 * h + 1),
        f ((rectangularPrismSiteEquiv m n h).symm p) :=
      (Equiv.sum_comp (rectangularPrismSiteEquiv m n h).symm f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rfl

theorem sum_comm_three
    {A B C R : Type*} [Fintype A] [Fintype B] [Fintype C]
    [AddCommMonoid R] (f : A -> B -> C -> R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem mul_mul_fintype_sum
    {A : Type*} [Fintype A] (a b : Real) (f : A -> Real) :
    a * b * (∑ x, f x) = ∑ x, a * b * f x := by
  rw [Finset.mul_sum]


end
end StatMech.Ising
