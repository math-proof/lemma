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
open Finset Real


noncomputable section

namespace SparseVarshamovGilbert

/-- Hamming distance between two binary vectors. -/
def hammingDist {d : ℕ} (ω₁ ω₂ : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω₁ i ≠ ω₂ i).card

/-- `ℓ⁰`-pseudonorm of a binary vector: number of `true` entries. -/
def l0norm {d : ℕ} (ω : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω i = true).card

end SparseVarshamovGilbert
end
