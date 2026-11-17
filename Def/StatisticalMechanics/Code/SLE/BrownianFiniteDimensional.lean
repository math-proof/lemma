/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

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
