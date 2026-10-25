/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_1_5_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_1_5_2
open MeasureTheory


noncomputable section

namespace Minimax

/-- A Gaussian sequence model: dimension `d`, sample size `n`, noise level `σ`,
parameter set `Θ ⊆ ℝ^d`, and a family of probability measures `P θ` on `ℝ^d` with
the standard KL-divergence formula `KL(P_θ₁ ‖ P_θ₀) = n‖θ₁ - θ₀‖² / (2σ²)`, plus
measurability/integrability hypotheses needed to talk about minimax risk. -/
structure GaussianSequenceModel where
  d : ℕ
  n : ℕ
  σ : ℝ
  hσ : 0 < σ
  hn : 0 < n
  Θ : Set (Fin d → ℝ)
  P : (Fin d → ℝ) → Measure (Fin d → ℝ)
  hP_prob : ∀ θ : Fin d → ℝ, IsProbabilityMeasure (P θ)
  hP_ac : ∀ θ₀ θ₁ : Fin d → ℝ, (P θ₀).AbsolutelyContinuous (P θ₁)
  hP_kl_toReal : ∀ θ₀ θ₁ : Fin d → ℝ,
    (InformationTheory.klDiv (P θ₁) (P θ₀)).toReal =
      n * sqDist θ₁ θ₀ / (2 * σ ^ 2)
  hP_kl_ne_top : ∀ θ₀ θ₁ : Fin d → ℝ,
    InformationTheory.klDiv (P θ₁) (P θ₀) ≠ ⊤
  hP_integrable : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
    MeasureTheory.Integrable (fun Y => sqDist (θhat Y) θ) (P θ)
  hP_aestronglyMeasurable : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
    MeasureTheory.AEStronglyMeasurable (fun Y => sqDist (θhat Y) θ) (P θ)
  hP_measurableSet_sqDist_ge : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ) (c : ℝ),
    MeasurableSet {Y | sqDist (θhat Y) θ ≥ c}
  hP_bddAbove : ∀ (Θ' : Set (Fin d → ℝ)) (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ'),
      ∫ Y, sqDist (θhat Y) θ ∂(P θ))
  hMeasurable_θhat : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)), Measurable θhat

end Minimax
end
