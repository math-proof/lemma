/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation.Part2
import Theorem.StatisticalMechanics.Code.SLE.BrownianContinuousModification.Part2
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

noncomputable def brownianContinuousModification (t : Real)
    (omega : Real -> Real) : Real :=
  brownianDyadicLimit (brownianCompactRadius t) t omega

end StatMech.SLE
