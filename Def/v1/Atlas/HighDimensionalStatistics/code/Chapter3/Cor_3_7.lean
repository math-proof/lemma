/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Setup
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_4
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Thm_3_4
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Thm_3_6
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open Matrix MeasureTheory


namespace Rigollet.Chapter3

/-- The empirical mean-squared error between an estimator `fhat` and the true regression
function `f` on the sample, `MSE = (1/n) ∑ᵢ (f̂ᵢ - fᵢ)²`. -/
noncomputable def MSE_37 {n : ℕ} (fhat f : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (fhat i - f i) ^ 2

/-- The support size (ℓ₀ "norm") of a coefficient vector `θ`, i.e. the number of
nonzero entries. -/
noncomputable def support_size_37 {M : ℕ} (θ : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- The ℓ¹ norm of a coefficient vector `θ`, `‖θ‖₁ = ∑ᵢ |θᵢ|`. -/
noncomputable def l1norm_37 {M : ℕ} (θ : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, |θ i|

/-- A dictionary (column-normalized design matrix) `Φ` satisfies the standard
normalization `∑ᵢ Φᵢⱼ² ≤ n` for every column `j`. -/
def DictNormalized {n M : ℕ} (Φ : Matrix (Fin n) (Fin M) ℝ) : Prop :=
  ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ (n : ℝ)

end Rigollet.Chapter3
