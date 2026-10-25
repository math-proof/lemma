/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Borel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Def.v1.Atlas.BooleanFunctions.code.GaussianStability.Part2
import Def.v1.Atlas.BooleanFunctions.code.Sheppard
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Sheppard
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.BorelCoordSymmetrization
import Def.v1.Atlas.BooleanFunctions.code.BorelCoordSymmetrization
set_option maxHeartbeats 800000


noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace GaussianStability

variable {n : ℕ}


def iterateSymmetrize {n : ℕ} (hn : 0 < n) :
    ℕ → (EuclideanSpace ℝ (Fin n) → ℝ) → (EuclideanSpace ℝ (Fin n) → ℝ)
  | 0, f => f
  | k + 1, f => if h : k < n then
      symmetrize_coord ⟨k, h⟩ (iterateSymmetrize hn k f)
    else iterateSymmetrize hn k f

end GaussianStability
end
