/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation.Part2
import Def.StatisticalMechanics.Code.SLE.BrownianContinuousModification
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

theorem neg_brownianCompactRadius_le (t : Real) :
    -(brownianCompactRadius t : Real) <= t := by
  apply neg_le_of_abs_le
  exact Nat.le_ceil |t|

theorem le_brownianCompactRadius (t : Real) :
    t <= brownianCompactRadius t := by
  exact (le_abs_self t).trans (Nat.le_ceil |t|)


end StatMech.SLE
