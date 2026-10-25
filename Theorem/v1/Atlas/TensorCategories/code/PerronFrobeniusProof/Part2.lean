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
import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof
open Finset BigOperators Matrix

set_option maxHeartbeats 800000


namespace PerronFrobenius

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- The Collatz-Wielandt set is closed. -/
lemma cwSet_closed (M : Matrix ι ι ℝ) : IsClosed (CWSet M) := by
  refine IsClosed.inter ((isClosed_stdSimplex ℝ ι).preimage continuous_fst) ?_
  refine IsClosed.inter (isClosed_le continuous_const continuous_snd) ?_
  change IsClosed {p : (ι → ℝ) × ℝ | ∀ i, p.2 * p.1 i ≤ M.mulVec p.1 i}
  rw [show {p : (ι → ℝ) × ℝ | ∀ i, p.2 * p.1 i ≤ M.mulVec p.1 i} =
      ⋂ i, {q : (ι → ℝ) × ℝ | q.2 * q.1 i ≤ M.mulVec q.1 i} from by ext; simp [Set.mem_iInter]]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_snd.mul ((continuous_apply i).comp continuous_fst))
      (continuous_mulVec_component M i)

omit [DecidableEq ι] [Nonempty ι] in
/-- The Collatz-Wielandt set is contained in the compact product of the standard simplex
and `[0, ∑ M i j]`. -/
lemma cwSet_subset_compact (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    CWSet M ⊆ (stdSimplex ℝ ι) ×ˢ (Set.Icc 0 (∑ i : ι, ∑ j : ι, M i j)) := by
  intro ⟨v, t⟩ ⟨hv, ht_nn, hle⟩
  exact ⟨hv, ht_nn,
    calc t = t * ∑ i, v i := by rw [hv.2, mul_one]
      _ = ∑ i, t * v i := mul_sum ..
      _ ≤ ∑ i, M.mulVec v i := sum_le_sum (fun i _ => hle i)
      _ ≤ ∑ i, ∑ j, M i j := by
          simp only [mulVec, dotProduct]
          exact sum_le_sum fun i _ => sum_le_sum fun j _ =>
            mul_le_of_le_one_right (le_of_lt (hM i j)) (simplex_le_one hv j)⟩

omit [DecidableEq ι] [Nonempty ι] in
/-- The Collatz-Wielandt set is compact. -/
lemma cwSet_compact (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    IsCompact (CWSet M) :=
  ((isCompact_stdSimplex ℝ ι).prod isCompact_Icc).of_isClosed_subset
    (cwSet_closed M) (cwSet_subset_compact M hM)

omit [DecidableEq ι] in
/-- The Collatz-Wielandt set is nonempty, witnessed by the uniform distribution paired
with `t = 0`. -/
lemma cwSet_nonempty (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    (CWSet M).Nonempty := by
  set n := Fintype.card ι
  set u : ι → ℝ := fun _ => (n : ℝ)⁻¹
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hu : u ∈ stdSimplex ℝ ι := ⟨fun _ => by positivity,
    by simp only [u, sum_const, card_univ, nsmul_eq_mul]
       exact mul_inv_cancel₀ (ne_of_gt hn)⟩
  exact ⟨⟨u, 0⟩,
    hu,
    le_refl _,
    fun i => by
      show (0 : ℝ) * u i ≤ M.mulVec u i
      rw [zero_mul]
      exact le_of_lt (by
        simp only [mulVec, dotProduct]
        exact sum_pos (fun j _ => mul_pos (hM i j) (by positivity)) univ_nonempty)⟩

end PerronFrobenius
