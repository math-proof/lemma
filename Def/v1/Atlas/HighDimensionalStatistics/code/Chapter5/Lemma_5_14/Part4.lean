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
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part2
open Finset Real


noncomputable section

namespace SparseVarshamovGilbert

/-- The `1`-sparse vector corresponding to coordinate `i`. -/
def sparseVecOfFin (d : ℕ) (i : Fin d) : SparseVec d 1 :=
  ⟨unitVec d i, l0norm_unitVec d i⟩

end SparseVarshamovGilbert
end
