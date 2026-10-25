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
import Def.StatisticalMechanics.Code.SLE.BrownianFiniteDimensional.Part2
open MeasureTheory Matrix ProbabilityTheory Set WithLp
open scoped ENNReal InnerProductSpace NNReal


namespace StatMech.SLE

theorem brownianCovarianceMatrix_eq_gram (I : Finset ℝ) :
    brownianCovarianceMatrix I = gram ℝ (fun t : I => brownianCovVector t) := rfl

theorem brownianCovarianceMatrix_posSemidef (I : Finset ℝ) :
    (brownianCovarianceMatrix I).PosSemidef := by
  rw [brownianCovarianceMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℝ _


end StatMech.SLE
