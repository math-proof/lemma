/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Thm_3_11
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.TrigOrtho
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_11

open Finset Real Set MeasureTheory

/-- The (infinite-dimensional) Sobolev ellipsoid `Θ(β, Q)`: the set of sequences `θ` such
that the weighted sum `∑ⱼ aⱼ² θⱼ²` (with Sobolev weights `aⱼ`) is summable and bounded by `Q`. -/
noncomputable def SobolevEllipsoidInf (β Q : ℝ) : Set (ℕ → ℝ) :=
  {θ | Summable (fun j : ℕ => (Chapter3.sobolevCoeff β (j + 1)) ^ 2 * (θ j) ^ 2) ∧
       ∑' j : ℕ, (Chapter3.sobolevCoeff β (j + 1)) ^ 2 * (θ j) ^ 2 ≤ Q}

/-- Equivalence between `ℕ` and the upper interval `Set.Ici n` via `k ↦ k + n`. -/
noncomputable def iciEquivNat (n : ℕ) : ℕ ≃ ↑(Set.Ici n) where
  toFun k := ⟨k + n, by simp [Set.mem_Ici]⟩
  invFun j := (↑j : ℕ) - n
  left_inv k := by simp
  right_inv j := by ext; exact Nat.sub_add_cancel j.prop
