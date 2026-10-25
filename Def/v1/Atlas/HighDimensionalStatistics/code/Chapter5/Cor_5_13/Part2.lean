/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.ExponentialBounds
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
import Instance.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13
open MeasureTheory InformationTheory


noncomputable section

namespace GaussianSequenceModel

/-- The identity estimator `θ̂(Y) = Y` (least squares in the Gaussian sequence model). -/
def identityEstimator (d : ℕ) : Estimator d := id

/-- Risk of an estimator `θ̂` at parameter `θ`: the expected squared distance
`E[‖θ̂(Y) - θ‖²]` under `P θ`. -/
def risk {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (θhat : Estimator d) (θ : Fin d → ℝ) : ℝ :=
  ∫ Y, sqDist (θhat Y) θ ∂(P θ)

/-- Worst-case risk of `θ̂` over the parameter set `Θ`. -/
def supRisk {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ : Set (Fin d → ℝ)) (θhat : Estimator d) : ℝ :=
  ⨆ θ ∈ Θ, risk P θhat θ

/-- Minimax risk over `Θ`: the infimum of the worst-case risk over all measurable estimators. -/
def minimaxRisk {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ : Set (Fin d → ℝ)) : ℝ :=
  ⨅ (θhat : { f : Estimator d // Measurable f }), supRisk P Θ θhat.val

/-- The `ℓ¹`-norm `|θ|_1 = ∑_i |θ_i|`. -/
def l1norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, |θ i|

end GaussianSequenceModel
end
