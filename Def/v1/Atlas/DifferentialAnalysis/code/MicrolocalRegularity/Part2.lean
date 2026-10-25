/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConeSupportCorollary
import Theorem.v1.Atlas.DifferentialAnalysis.code.ConeSupportCorollary
import Structure.v1.Atlas.DifferentialAnalysis.code.MicrolocalRegularity


noncomputable section

open scoped SchwartzMap

namespace WavefrontSet

variable {n : ℕ}


/-- Pairing of distributions `u₁, u₂` with disjoint conic singular supports, defined via a
specified conic cutoff `ψ₁`: applies `u₁` to the Schwartz representative of `ψ₁ · u₂` and `u₂` to
the Schwartz representative of `(1 - ψ₁) · u₁`, then sums. -/
def cssPairingWith {K₁ K₂ : Set (ClosedBall n)}
    (ψ₁ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) : ℂ :=
  u₁ (toSchwartzOfEmptyCss _ (hψ.schwartz_of_mul u₂ h₂)) +
  u₂ (toSchwartzOfEmptyCss _ (hψ.schwartz_of_compl_mul u₁ h₁))

end WavefrontSet
end
