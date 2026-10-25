/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CommutatorEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.EllipticLowerBound
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.EllipticLowerBound
open scoped SchwartzMap
open TemperedDistribution MvPolynomial


noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

/-- A smooth radial cutoff on `Fin n → ℝ`: a continuous function taking values
in `[0, 1]` that is identically `1` on the closed unit ball and has compact
support.  Used to remove the singularity of `1/P_m(ξ)` at the origin in
the parametrix construction. -/
structure SmoothCutoff (n : ℕ) where
  toFun : (Fin n → ℝ) → ℝ
  eq_one_near_zero : ∀ ξ : Fin n → ℝ, ‖ξ‖ ≤ 1 → toFun ξ = 1
  hasCompactSupport : HasCompactSupport toFun
  nonneg : ∀ ξ, 0 ≤ toFun ξ
  le_one : ∀ ξ, toFun ξ ≤ 1
  continuous_toFun : Continuous toFun

end DifferentialOperators
end
