/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
open Finset Real


noncomputable section

namespace SparseVarshamovGilbert

/-- A canonical `k`-sparse vector: the indicator of `{i : Fin d | i.val < k}`. -/
def mkSparseVec (d k : ℕ) (hkd : k ≤ d) : SparseVec d k :=
  ⟨fun i => decide (i.val < k), by
    simp only [l0norm, decide_eq_true_eq]; exact card_filter_val_lt d k hkd⟩

/-- Variant of `sparseBall` using the ceiling-style radius `(k+1)/2`. -/
def sparseBallCeil (d k : ℕ) (x : SparseVec d k) : Finset (SparseVec d k) :=
  Finset.univ.filter fun y => hammingDist x.val y.val < (k + 1) / 2

/-- Support of a binary vector: the finset of indices `i` with `f i = true`. -/
def supp {d : ℕ} (f : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter fun i => f i = true

/-- The `i`-th standard binary unit vector in `{0,1}^d`. -/
def unitVec (d : ℕ) (i : Fin d) : Fin d → Bool := fun j => i == j

end SparseVarshamovGilbert
end
