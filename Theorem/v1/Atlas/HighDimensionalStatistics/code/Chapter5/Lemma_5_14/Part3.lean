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
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part4
open Finset Real


noncomputable section

namespace SparseVarshamovGilbert

/-- `|{i : Fin d | a ≤ i.val < a + k}| = k` when `a + k ≤ d`. -/
lemma card_filter_interval (d a k : ℕ) (h : a + k ≤ d) :
    (Finset.univ.filter (fun i : Fin d => a ≤ i.val ∧ i.val < a + k)).card = k := by
  have hmk : ∀ m : Fin k, a + m.val < d := fun ⟨m, hm⟩ => by omega
  let f : Fin k → Fin d := fun m => ⟨a + m.val, hmk m⟩
  have hf_inj : Function.Injective f := by intro x y hab; ext; simp [f] at hab; omega
  have himg : (Finset.univ.filter (fun i : Fin d => a ≤ i.val ∧ i.val < a + k)) =
    (Finset.univ : Finset (Fin k)).image f := by
    ext ⟨i, _⟩; constructor
    · intro hmem; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      simp only [Finset.mem_image, Finset.mem_univ, true_and, f, Fin.ext_iff]
      exact ⟨⟨i - a, by omega⟩, by simp; omega⟩
    · intro hmem; simp only [Finset.mem_image, Finset.mem_univ, true_and, f, Fin.ext_iff] at hmem
      obtain ⟨⟨m, _⟩, hval⟩ := hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp at hval; omega
  rw [himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]

end SparseVarshamovGilbert
end
