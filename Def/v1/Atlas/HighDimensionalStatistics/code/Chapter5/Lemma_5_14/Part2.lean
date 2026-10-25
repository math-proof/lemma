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
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
open Finset Real


noncomputable section

namespace SparseVarshamovGilbert

/-- The "ball" of `k`-sparse vectors at Hamming distance strictly less than `k/2` (integer
division) from `x`. -/
def sparseBall (d k : ℕ) (x : SparseVec d k) : Finset (SparseVec d k) :=
  Finset.univ.filter fun y => hammingDist x.val y.val < k / 2

end SparseVarshamovGilbert
end
