/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveExtension.Part2
import Theorem.StatisticalMechanics.Code.SLE.BrownianMomentBound
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianProductProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal


namespace StatMech.SLE

instance brownianFiniteDimensionalPiLaw.isGaussian (I : Finset Real) :
    IsGaussian (brownianFiniteDimensionalPiLaw I) := by
  unfold brownianFiniteDimensionalPiLaw
  change IsGaussian ((brownianFiniteDimensionalLaw I).map
    (PiLp.continuousLinearEquiv 2 Real (fun _ : I => Real)))
  infer_instance


end StatMech.SLE
