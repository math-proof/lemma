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
public import Def.StatisticalMechanics.Code.SLE.BrownianFiniteDimensional.Part3
@[expose] public section

open MeasureTheory Matrix ProbabilityTheory Set WithLp
open scoped ENNReal InnerProductSpace NNReal


namespace StatMech.SLE

instance brownianFiniteDimensionalLaw.isProbabilityMeasure (I : Finset ℝ) :
    IsProbabilityMeasure (brownianFiniteDimensionalLaw I) := by
  unfold brownianFiniteDimensionalLaw
  infer_instance

instance brownianFiniteDimensionalLaw.isGaussian (I : Finset ℝ) :
    IsGaussian (brownianFiniteDimensionalLaw I) := by
  unfold brownianFiniteDimensionalLaw
  infer_instance

end StatMech.SLE
