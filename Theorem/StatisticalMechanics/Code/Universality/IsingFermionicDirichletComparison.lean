/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteGraphLaplacian_add_const
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f : V → ℝ) (c : ℝ) (x : V) :
    isingFiniteGraphLaplacian G (fun y ↦ f y + c) x =
      isingFiniteGraphLaplacian G f x := by
  classical
  unfold isingFiniteGraphLaplacian
  apply Finset.sum_congr rfl
  intro y hy
  ring


theorem isingFiniteGraphLaplacian_add
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f g : V → ℝ) (x : V) :
    isingFiniteGraphLaplacian G (fun y ↦ f y + g y) x =
      isingFiniteGraphLaplacian G f x +
        isingFiniteGraphLaplacian G g x := by
  classical
  unfold isingFiniteGraphLaplacian
  simp only []
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  ring


theorem isingFiniteGraphLaplacian_const_mul
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : ℝ) (f : V → ℝ) (x : V) :
    isingFiniteGraphLaplacian G (fun y ↦ c * f y) x =
      c * isingFiniteGraphLaplacian G f x := by
  classical
  unfold isingFiniteGraphLaplacian
  simp only []
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring


end
end StatMech.Universality
