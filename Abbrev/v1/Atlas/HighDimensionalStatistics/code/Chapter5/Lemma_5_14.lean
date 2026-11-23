/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
open Finset Real


@[expose] public noncomputable section

namespace SparseVarshamovGilbert

/-- Type of `k`-sparse binary vectors in `{0,1}^d`. -/
abbrev SparseVec (d k : ℕ) := {f : Fin d → Bool // l0norm f = k}

end SparseVarshamovGilbert
end
