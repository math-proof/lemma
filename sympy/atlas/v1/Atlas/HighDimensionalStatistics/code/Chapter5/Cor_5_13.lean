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
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8

open MeasureTheory InformationTheory

noncomputable section

namespace GaussianSequenceModel

/-- Squared Euclidean distance between two vectors in `ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- An estimator is a function mapping observations in `ℝ^d` to a parameter estimate in `ℝ^d`. -/
def Estimator (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

/-- `Estimator d` is nonempty (witnessed by the identity). -/
instance {d : ℕ} : Nonempty (Estimator d) := ⟨id⟩

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

/-- Structural property recording that a family `P : ℝ^d → Measure ℝ^d` is a Gaussian sequence
model with noise level `σ` and sample size `n`: each `P θ` is a probability measure with the
expected coordinate-wise variance, mean, KL/density-ratio structure, and integrability
properties required to run the minimax arguments of Chapter 5. -/
structure IsGSM {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (n : ℕ) : Prop where
  isProbabilityMeasure : ∀ (hσ : 0 < σ) (hn : 0 < n) (θ : Fin d → ℝ),
    IsProbabilityMeasure (P θ)
  identity_risk_coord : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ : Fin d → ℝ) (i : Fin d),
    ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n
  coord_mean : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ : Fin d → ℝ) (i : Fin d),
    ∫ Y, Y i ∂(P θ) = θ i
  density_ratio : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ₁ θ₂ : Fin d → ℝ), P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (Real.exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2))))
  integrable_sqDist : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
    Integrable (fun Y => sqDist (θhat Y) θ) (P θ)
  bddAbove_risk : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
      ∫ Y, sqDist (θhat Y) θ ∂(P θ))
  hP_kl_ne_top : ∀ (θ₀ θ₁ : Fin d → ℝ),
    InformationTheory.klDiv (P θ₁) (P θ₀) ≠ ⊤

  expected_cross_term_bound : ∀ (hσ : 0 < σ) (hn : 0 < n) (hd : 0 < d)
    (R : ℝ) (hR : 0 < R)
    (θ θ' : Fin d → ℝ)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ))
    (hθ' : l1norm θ' ≤ R)
    (hθhat : ∀ Y, l1norm (θhat Y) ≤ R),
    ∫ Y, ∑ i : Fin d, (θhat Y i - θ' i) * (Y i - θ i) ∂(P θ) ≤
      (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ)
  integrable_cross_term : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ θ' : Fin d → ℝ),
    Integrable (fun Y => ∑ i : Fin d, (θhat Y i - θ' i) * (Y i - θ i)) (P θ)

/-- The real vector with entry `s` at positions where `ω i = true` and `0` elsewhere. -/
def scaledBoolVec {d : ℕ} (ω : Fin d → Bool) (s : ℝ) : Fin d → ℝ :=
  fun i => if ω i then s else 0
