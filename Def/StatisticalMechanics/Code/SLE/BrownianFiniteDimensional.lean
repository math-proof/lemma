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
open MeasureTheory Matrix ProbabilityTheory Set WithLp
open scoped ENNReal InnerProductSpace NNReal


namespace StatMech.SLE

noncomputable def brownianCovVector (t : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (s := uIoc 0 t) measurableSet_uIoc
    (by
      simp only [uIoc]
      exact (measure_Ioc_lt_top (μ := (volume : Measure ℝ))).ne) 1


noncomputable def brownianCovariance (s t : ℝ) : ℝ :=
  ⟪brownianCovVector s, brownianCovVector t⟫_ℝ

end StatMech.SLE
