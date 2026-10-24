/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Mathlib

open MeasureTheory Matrix Real Finset

namespace Rigollet.Chapter4.Thm_4_4

noncomputable section

/-- Squared Frobenius norm, $\sum_{i,j} A_{ij}^2$. -/
def frobeniusNormSq {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin p, (A i j) ^ 2

/-- Frobenius (entrywise) inner product of two matrices. -/
def frobeniusInner {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin p, A i j * B i j

/-- Rank-penalized least-squares objective:
$\frac{1}{n}\|Y - X\Theta\|_F^2 + 2\tau^2 \cdot \mathrm{rank}(\Theta)$. -/
def rankPenObjective {n d T : ℕ}
    (Y : Matrix (Fin n) (Fin T) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (τ : ℝ) (Θ : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  (1 / (n : ℝ)) * frobeniusNormSq (Y - X * Θ) + 2 * τ ^ 2 * (Θ.rank : ℝ)

/-- `Θhat` is a rank-penalized estimator if it minimizes `rankPenObjective`. -/
def IsRankPenalizationEstimator {n d T : ℕ}
    (Y : Matrix (Fin n) (Fin T) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (τ : ℝ) (Θhat : Matrix (Fin d) (Fin T) ℝ) : Prop :=
  ∀ Θ : Matrix (Fin d) (Fin T) ℝ,
    rankPenObjective Y X τ Θhat ≤ rankPenObjective Y X τ Θ

/-- Prediction MSE: $\frac{1}{n}\|X\hat\Theta - X\Theta^*\|_F^2$. -/
def predictionMSE {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  (1 / (n : ℝ)) * frobeniusNormSq (X * Θhat - X * Θstar)
