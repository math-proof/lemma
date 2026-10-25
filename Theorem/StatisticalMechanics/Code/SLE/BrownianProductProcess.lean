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
import Def.StatisticalMechanics.Code.SLE.BrownianProductProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal


namespace StatMech.SLE

theorem brownianCoordinateProcess_measurable (t : Real) :
    Measurable (brownianCoordinateProcess t) := by
  change Measurable (fun omega : Real -> Real => omega t)
  fun_prop

end StatMech.SLE
