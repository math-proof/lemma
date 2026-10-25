/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter2.Thm_2_4
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_4
import Mathlib
open Matrix MeasureTheory Metric Set Real ENNReal Finset


noncomputable section

/-- Identification `Fin n → ℝ → EuclideanSpace ℝ (Fin n)` used to switch between
pointwise and Euclidean representations. -/
abbrev toEuc (n : ℕ) : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm

/-- Inverse of `toEuc`: forgets the Euclidean structure. -/
abbrev fromEuc (n : ℕ) : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) :=
  (WithLp.equiv 2 (Fin n → ℝ))

end
