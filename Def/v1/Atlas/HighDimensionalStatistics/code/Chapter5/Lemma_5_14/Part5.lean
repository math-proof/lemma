module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
public import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part3
open Finset Real


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace SparseVarshamovGilbert

/-- The `j`-th block of `k` consecutive indices, packaged as a `k`-sparse vector. -/
def blockSparseVec (d k : ℕ) (hkd : k ≤ d / 8) (j : Fin 8) : SparseVec d k :=
  ⟨fun i => decide (j.val * k ≤ i.val ∧ i.val < j.val * k + k), by
    simp only [l0norm, decide_eq_true_eq]
    apply card_filter_interval
    have h1 : 8 * k ≤ d := by have := Nat.div_mul_le_self d 8; omega
    nlinarith [j.isLt]⟩

end SparseVarshamovGilbert
end
