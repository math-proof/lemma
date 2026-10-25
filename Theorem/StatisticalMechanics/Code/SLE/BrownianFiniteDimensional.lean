/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Def.StatisticalMechanics.Code.SLE.BrownianFiniteDimensional
open MeasureTheory Matrix ProbabilityTheory Set WithLp
open scoped ENNReal InnerProductSpace NNReal


namespace StatMech.SLE

theorem brownianCovariance_eq_volumeReal (s t : ℝ) :
    brownianCovariance s t =
      (volume : Measure ℝ).real (uIoc 0 s ∩ uIoc 0 t) := by
  simp [brownianCovariance, brownianCovVector,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]


theorem brownianCovariance_eq (s t : ℝ) :
    brownianCovariance s t = (|s| + |t| - |t - s|) / 2 := by
  rw [brownianCovariance_eq_volumeReal, uIoc, uIoc, Ioc_inter_Ioc,
    Real.volume_real_Ioc]
  rcases le_total 0 s with hs | hs <;>
    rcases le_total 0 t with ht | ht <;>
      rcases le_total s t with hst | hst
  all_goals simp [hs, ht, hst, abs_of_nonneg, abs_of_nonpos] <;> linarith

@[simp]
theorem brownianCovariance_self (t : ℝ) : brownianCovariance t t = |t| := by
  rw [brownianCovariance_eq_volumeReal, inter_self, Measure.real]
  simp [Real.volume_uIoc]

@[simp]
theorem brownianCovariance_zero_left (t : ℝ) : brownianCovariance 0 t = 0 := by
  rw [brownianCovariance_eq_volumeReal]
  simp

@[simp]
theorem brownianCovariance_zero_right (t : ℝ) : brownianCovariance t 0 = 0 := by
  rw [brownianCovariance_eq_volumeReal]
  simp

theorem brownianCovariance_symm (s t : ℝ) :
    brownianCovariance s t = brownianCovariance t s := by
  simp only [brownianCovariance, real_inner_comm]


end StatMech.SLE
