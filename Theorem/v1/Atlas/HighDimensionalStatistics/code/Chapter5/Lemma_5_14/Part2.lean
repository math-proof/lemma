module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part3
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

/-- The `ℓ⁰`-norm of `unitVec d i` is `1`. -/
lemma l0norm_unitVec (d : ℕ) (i : Fin d) : l0norm (unitVec d i) = 1 := by
  unfold l0norm unitVec
  simp only [beq_iff_eq]
  have : (Finset.univ.filter fun j : Fin d => i = j) = {i} := by
    ext j; simp [eq_comm]
  rw [this, card_singleton]

end SparseVarshamovGilbert
end
