/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Setup
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter2.Lemma_2_17
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Lemma_2_17
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Chebyshev
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Matrix Finset MeasureTheory


namespace Rigollet.Chapter3

/-- Squared Euclidean norm of a real vector `v : Fin n → ℝ`. -/
noncomputable def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- Mean-squared error between an estimator `fhat` and a target `f` over
`n` design points: `MSE = (1/n) · Σᵢ (fhatᵢ − fᵢ)²`. -/
noncomputable def MSE_35 {n : ℕ} (fhat f : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (fhat i - f i) ^ 2

/-- The `ℓ₀` "sparsity" of a vector `θ`: the number of nonzero entries. -/
noncomputable def support_size_35 {M : ℕ} (θ : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- The `ℓ¹` norm of a vector `θ : Fin M → ℝ`. -/
noncomputable def l1norm_35 {M : ℕ} (θ : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, |θ i|

/-- Least-squares objective for the design matrix `Φ` and response `Y`:
`(1/n) · ‖Y − Φθ‖²`. -/
noncomputable def lsObjective_35 {n M : ℕ} (Y : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (θ : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (Y i - (Φ.mulVec θ) i) ^ 2

/-- Lasso objective: least-squares loss plus `2τ‖θ‖₁` penalty. -/
noncomputable def lassoObjective_35 {n M : ℕ} (Y : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (τ : ℝ) (θ : Fin M → ℝ) : ℝ :=
  lsObjective_35 Y Φ θ + 2 * τ * l1norm_35 θ

/-- The cone condition relative to the support `S`: the off-support `ℓ¹` mass
of `Δ` is at most `3` times the on-support `ℓ¹` mass. -/
def ConeCondition {M : ℕ} (Δ : Fin M → ℝ) (S : Finset (Fin M)) :
    Prop :=
  ∑ j ∈ Finset.univ \ S, |Δ j| ≤ 3 * ∑ j ∈ S, |Δ j|

/-- The incoherence condition `INC(k)` of the design matrix `Φ`, used to
guarantee restricted invertibility on `k`-sparse vectors. -/
def INC_condition {n M : ℕ} (Φ : Matrix (Fin n) (Fin M) ℝ) (k : ℕ) : Prop :=
  AssumptionINC Φ k

/-- The noise vector `ε` is coordinate-wise sub-Gaussian with parameter `σ`:
each `εᵢ` has MGF bounded by `exp(σ²s²/2)`. -/
def IsSubGaussianNoise {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ε : Ω → Fin n → ℝ) (σ : ℝ) (μ : Measure Ω) : Prop :=
  ∀ i : Fin n, ∀ s : ℝ,
    ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σ ^ 2 * s ^ 2 / 2)

end Rigollet.Chapter3
