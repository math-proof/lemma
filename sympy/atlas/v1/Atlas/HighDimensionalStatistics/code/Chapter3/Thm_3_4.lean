/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Setup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Matrix MeasureTheory

namespace Rigollet.Chapter3

/-- Empirical mean-squared error `MSE = (1/n) ∑ᵢ (f̂ᵢ - fᵢ)²` used in Theorem 3.4. -/
noncomputable def MSE_34 {n : ℕ} (fhat f : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (fhat i - f i) ^ 2

/-- The support size (ℓ₀ norm) `|θ|₀ = #{i : θᵢ ≠ 0}` used in Theorem 3.4. -/
noncomputable def support_size_34 {M : ℕ} (θ : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- Sub-Gaussian noise condition via the moment generating function: for every unit
vector `v` and every `s ∈ ℝ`, the MGF of `⟨ε, v⟩` is bounded by `exp(s² σ² / 2)`. -/
def IsSubGaussianNoiseMGF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (ε : Ω → Fin n → ℝ) (σsq : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, dotProduct v v = 1 →
    ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * σsq / 2)
