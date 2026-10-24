/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Thm_3_15
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Thm_3_4
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Thm_3_5
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_15
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_4
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_5
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6

set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory

namespace Chapter3

/-- `θhat` is a BIC estimator for the trigonometric model with penalty parameter `τ²`:
for every `ω` it minimizes empirical squared error plus `τ²` times the support size
of the coefficient vector. -/
def IsBICEstimatorTrig {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) (τsq : ℝ) : Prop :=
  ∀ ω θ,
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 +
      τsq * ↑((Finset.univ.filter (fun j => θhat ω j ≠ 0)).card) ≤
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ))) ^ 2 +
      τsq * ↑((Finset.univ.filter (fun j => θ j ≠ 0)).card)

/-- `θhat` is a Lasso estimator for the trigonometric model with regularization parameter
`τ`: for every `ω` it minimizes empirical squared error plus `2τ` times the `ℓ¹` norm of
the coefficient vector. -/
def IsLassoEstimatorTrig {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) (τ : ℝ) : Prop :=
  ∀ ω θ,
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 +
      2 * τ * ∑ j : Fin (n - 1), |θhat ω j| ≤
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ))) ^ 2 +
      2 * τ * ∑ j : Fin (n - 1), |θ j|

/-- `θhat` is either a BIC or Lasso estimator with some positive tuning parameter. -/
def IsBICOrLassoEstimator {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) : Prop :=
  (∃ τsq : ℝ, 0 < τsq ∧ IsBICEstimatorTrig Y θhat τsq) ∨
  (∃ τ : ℝ, 0 < τ ∧ IsLassoEstimatorTrig Y θhat τ)
