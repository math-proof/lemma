module
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Def.StatisticalMechanics.Code.SLE.BrownianFiniteDimensional.Part4
open MeasureTheory Matrix ProbabilityTheory Set WithLp
open scoped ENNReal InnerProductSpace NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

instance brownianFiniteDimensionalPiLaw.isProbabilityMeasure (I : Finset ℝ) :
    IsProbabilityMeasure (brownianFiniteDimensionalPiLaw I) := by
  unfold brownianFiniteDimensionalPiLaw
  infer_instance


end StatMech.SLE
