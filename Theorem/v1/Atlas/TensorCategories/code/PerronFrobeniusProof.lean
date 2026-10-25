/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobeniusProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.StdSimplex
open Finset BigOperators Matrix

set_option maxHeartbeats 800000


namespace PerronFrobenius

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- Continuity of the `i`-th component of `M.mulVec` as a function of `(v, t)`. -/
lemma continuous_mulVec_component (M : Matrix ι ι ℝ) (i : ι) :
    Continuous (fun p : (ι → ℝ) × ℝ => M.mulVec p.1 i) := by
  simp only [mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_fst)

omit [DecidableEq ι] [Nonempty ι] in
/-- Each coordinate of a point in the standard simplex is bounded above by `1`. -/
lemma simplex_le_one {v : ι → ℝ} (hv : v ∈ stdSimplex ℝ ι) (i : ι) : v i ≤ 1 :=
  le_trans (single_le_sum (fun k _ => hv.1 k) (mem_univ i)) (le_of_eq hv.2)

omit [DecidableEq ι] [Nonempty ι] in
/-- For a strictly positive matrix `M` and any point in the standard simplex, every
coordinate of `M.mulVec v` is strictly positive. -/
lemma mulVec_pos (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    {v : ι → ℝ} (hv : v ∈ stdSimplex ℝ ι) (i : ι) :
    0 < M.mulVec v i := by
  simp only [mulVec, dotProduct]
  have ⟨j, hj⟩ : ∃ j, 0 < v j := by
    by_contra h; push Not at h
    linarith [hv.2, sum_nonpos (fun j (_ : j ∈ univ) => h j)]
  calc 0 < M i j * v j := mul_pos (hM i j) hj
    _ ≤ ∑ k, M i k * v k :=
        single_le_sum (fun k _ => mul_nonneg (le_of_lt (hM i k)) (hv.1 k)) (mem_univ j)

end PerronFrobenius
