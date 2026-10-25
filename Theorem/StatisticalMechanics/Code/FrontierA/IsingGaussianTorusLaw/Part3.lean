/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part4
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusLaw.Part3
open Finset MeasureTheory
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising

noncomputable section

variable {d k : Nat}


theorem integral_exp_isingTorusSmearedSpin_le
    (beta : Real) (hbeta : 0 < beta)
    (f h : IsingDyadicTorus d k -> Real)
    (hpotential : forall u : IsingDyadicTorus d k -> Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∫ sigma, Real.exp (s * isingTorusSmearedSpin f sigma)
        ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
          ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <=
      Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  rw [integral_isingTorusZeroFieldLaw]
  unfold isingTorusZeroFieldMass isingTorusSmearedSpin
  calc
    (∑ sigma,
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) /
          isingTorusShiftedPartition beta 0 *
            Real.exp (s * ∑ x, isingTorusSpinField sigma x * f x)) =
        (∑ sigma,
          Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
              Real.exp (s * ∑ x,
                isingTorusSpinField sigma x * f x)) /
          isingTorusShiftedPartition beta 0 := by
      rw [Finset.sum_div Finset.univ]
      apply Finset.sum_congr rfl
      intro sigma _
      ring
    _ <= _ := isingTorus_linear_expMoment_le_unconditional
      beta hbeta f h hpotential s


theorem integral_exp_abs_isingTorusSmearedSpin_le
    (beta : Real) (hbeta : 0 < beta)
    (f h : IsingDyadicTorus d k -> Real)
    (hpotential : forall u : IsingDyadicTorus d k -> Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∫ sigma, Real.exp (s * |isingTorusSmearedSpin f sigma|)
        ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
          ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <=
      2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  rw [integral_isingTorusZeroFieldLaw]
  unfold isingTorusZeroFieldMass isingTorusSmearedSpin
  calc
    (∑ sigma,
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) /
          isingTorusShiftedPartition beta 0 *
            Real.exp (s * |∑ x,
              isingTorusSpinField sigma x * f x|)) =
        (∑ sigma,
          Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
              Real.exp (s * |∑ x,
                isingTorusSpinField sigma x * f x|)) /
          isingTorusShiftedPartition beta 0 := by
      rw [Finset.sum_div Finset.univ]
      apply Finset.sum_congr rfl
      intro sigma _
      ring
    _ <= _ := isingTorus_linear_expAbsMoment_le_unconditional
      beta hbeta f h hpotential s


theorem exists_isingTorusSmearedSpin_expMoment_bounds
    (beta : Real) (hbeta : 0 < beta)
    (f : IsingDyadicTorus d k -> Real) (hzero : ∑ x, f x = 0) :
    ∃ h : IsingDyadicTorus d k -> Real,
      (forall u : IsingDyadicTorus d k -> Real,
        isingTorusDirichletBilinear u h = ∑ x, u x * f x) ∧
      (forall s : Real,
        (∫ sigma, Real.exp (s * isingTorusSmearedSpin f sigma)
            ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
              ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <=
          Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta))) ∧
      (forall s : Real,
        (∫ sigma, Real.exp (s * |isingTorusSmearedSpin f sigma|)
            ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
              ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <=
          2 * Real.exp
            (s ^ 2 * isingTorusDirichlet h / (2 * beta))) := by
  obtain ⟨h, hpotential⟩ := exists_isingTorusDirichlet_potential f hzero
  exact ⟨h, hpotential,
    fun s => integral_exp_isingTorusSmearedSpin_le
      beta hbeta f h hpotential s,
    fun s => integral_exp_abs_isingTorusSmearedSpin_le
      beta hbeta f h hpotential s⟩

end
end StatMech.FrontierA
