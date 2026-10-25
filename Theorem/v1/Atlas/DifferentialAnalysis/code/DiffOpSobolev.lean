/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevDerivatives
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevDerivatives
import Mathlib.Algebra.MvPolynomial.Degrees
import Def.v1.Atlas.DifferentialAnalysis.code.DiffOpSobolev.Part2
open scoped SchwartzMap ContDiff FourierTransform
open DifferentialOperators SobolevEmbedding SobolevSpace MvPolynomial Filter Topology MeasureTheory


noncomputable section

namespace DiffOpSobolev

variable (n : ℕ)

/-- If `k ≥ n`, the tail sum `∑_{i ≥ k} α i` is empty and hence `0`. -/
lemma tailMultiIndexSum_ge {n : ℕ} (α : Fin n → ℕ) (k : ℕ) (hk : n ≤ k) :
    tailMultiIndexSum α k = 0 := by
  simp only [tailMultiIndexSum]
  apply Finset.sum_eq_zero
  intro i hi
  simp [Finset.mem_filter] at hi
  omega

/-- Recurrence for the tail sum: peel off the term at index `k`. -/
lemma tailMultiIndexSum_succ {n : ℕ} (α : Fin n → ℕ) (k : ℕ) (hk : k < n) :
    tailMultiIndexSum α k = α ⟨k, hk⟩ + tailMultiIndexSum α (k + 1) := by
  simp only [tailMultiIndexSum]
  have hsplit : Finset.univ.filter (fun j : Fin n => k ≤ j.val) =
      {⟨k, hk⟩} ∪ Finset.univ.filter (fun j : Fin n => k + 1 ≤ j.val) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hxk : x.val = k
      · left; exact Fin.ext hxk
      · right; omega
    · intro hx
      rcases hx with hx | hx
      · subst hx; simp
      · omega
  rw [hsplit, Finset.sum_union]
  · simp
  · rw [Finset.disjoint_singleton_left]
    simp [Finset.mem_filter]

end DiffOpSobolev
end
