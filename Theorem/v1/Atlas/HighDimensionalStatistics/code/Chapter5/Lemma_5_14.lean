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
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part2
open Finset Real


noncomputable section

namespace SparseVarshamovGilbert

/-- There are exactly `k` indices `i : Fin d` with `i.val < k` (assuming `k ≤ d`). -/
lemma card_filter_val_lt (d k : ℕ) (hkd : k ≤ d) :
    (Finset.univ.filter (fun i : Fin d => i.val < k)).card = k := by
  rcases Nat.eq_or_lt_of_le hkd with hkd' | hkd'
  · have : (Finset.univ.filter (fun i : Fin d => i.val < k)) = Finset.univ := by
      ext i; simp [hkd']
    rw [this, Finset.card_univ, Fintype.card_fin]; omega
  · convert Fin.card_Iio (⟨k, hkd'⟩ : Fin d) using 1
    congr 1; ext ⟨i, hi⟩; simp [Finset.mem_filter, Finset.mem_Iio, Fin.lt_def]

end SparseVarshamovGilbert
end
