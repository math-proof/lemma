/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingReflectionKernel
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Mathlib.Analysis.Calculus.Taylor
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination
open Finset Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising


variable {d k : Nat}


theorem isingTorusDirichletBilinear_symm
    (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear u v =
      isingTorusDirichletBilinear v u := by
  unfold isingTorusDirichletBilinear
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isingTorusDirichletBilinear_add_left
    (u v w : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear (u + v) w =
      isingTorusDirichletBilinear u w +
        isingTorusDirichletBilinear v w := by
  unfold isingTorusDirichletBilinear
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isingTorusDirichletBilinear_smul_left
    (t : Real) (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear (t • u) v =
      t * isingTorusDirichletBilinear u v := by
  unfold isingTorusDirichletBilinear
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isingTorusDirichlet_add
    (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (u + v) =
      isingTorusDirichlet u +
        2 * isingTorusDirichletBilinear u v +
        isingTorusDirichlet v := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  simp only [Pi.add_apply]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isingTorusDirichlet_smul
    (t : Real) (u : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (t • u) =
      t ^ 2 * isingTorusDirichlet u := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring


theorem isingTorusShiftedPartition_smul
    (beta t : Real) (h : IsingDyadicTorus d k → Real) :
    isingTorusShiftedPartition beta (t • h) =
      Real.exp (-(beta / 2) * t ^ 2 * isingTorusDirichlet h) *
        ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
          Real.exp (-beta * t *
            isingTorusDirichletBilinear
              (isingTorusSpinField sigma) h) := by
  unfold isingTorusShiftedPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [isingTorusDirichlet_add,
    isingTorusDirichlet_smul,
    isingTorusDirichletBilinear_symm
      (isingTorusSpinField sigma) (t • h),
    isingTorusDirichletBilinear_smul_left,
    isingTorusDirichletBilinear_symm h (isingTorusSpinField sigma),
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem isingTorusShiftedPartition_zero_pos (beta : Real) :
    0 < isingTorusShiftedPartition (d := d) (k := k) beta 0 := by
  unfold isingTorusShiftedPartition
  exact Finset.sum_pos (fun sigma _ => Real.exp_pos _) Finset.univ_nonempty


end StatMech.FrontierA
