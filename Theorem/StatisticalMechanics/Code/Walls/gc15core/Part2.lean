/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
import Def.StatisticalMechanics.Code.Walls.gc15core
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (S : SimpleGraph V) [DecidableRel S.Adj]


theorem gc15_inner_fiber_triple (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B C : Finset V) :
    (∑ K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
        ((if sources S (ofEdgeFun S K.1.1) = A then weight S β J (ofEdgeFun S K.1.1) else 0) *
          (if sources S (ofEdgeFun S K.1.2) = B then weight S β J (ofEdgeFun S K.1.2) else 0)) *
          (if sources S (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) = C
            then weight S β J (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) else 0))
      = gc15_tFiber S β J A B C m := by
  unfold gc15_tFiber gc15_tpsum
  by_cases hm : sources S (ofEdgeFun S m) = A ∆ B ∆ C
  · rw [if_pos hm]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    by_cases hA : sources S (ofEdgeFun S K.1.1) = A
    · by_cases hB : sources S (ofEdgeFun S K.1.2) = B
      · simp only [if_pos hA, if_pos hB]
        have hcompl : sources S (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) = C := by
          have hadd := sources_ofEdgeFun_add₃ S m K.1.1 K.1.2 K.2
          rw [hA, hB, hm] at hadd
          exact (symmDiff_right_injective (A ∆ B) hadd).symm
        rw [if_pos hcompl]
      · simp only [if_neg hB, mul_zero, zero_mul]
    · simp only [if_neg hA, zero_mul, zero_mul]
  · rw [if_neg hm]
    refine Finset.sum_eq_zero (fun K _ => ?_)
    by_cases hA : sources S (ofEdgeFun S K.1.1) = A
    · by_cases hB : sources S (ofEdgeFun S K.1.2) = B
      · simp only [if_pos hA, if_pos hB]
        by_cases hcompl : sources S (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) = C
        · exact absurd (by rw [sources_ofEdgeFun_add₃ S m K.1.1 K.1.2 K.2, hA, hB, hcompl]) hm
        · rw [if_neg hcompl, mul_zero]
      · simp only [if_neg hB, mul_zero, zero_mul]
    · simp only [if_neg hA, zero_mul, zero_mul]


theorem gc15_summable_tFiber (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    Summable (gc15_tFiber S β J A B C) := by
  set f : (↥S.edgeFinset → ℕ) → ℝ :=
    fun p => if sources S (ofEdgeFun S p) = A then weight S β J (ofEdgeFun S p) else 0 with hf
  set g : (↥S.edgeFinset → ℕ) → ℝ :=
    fun p => if sources S (ofEdgeFun S p) = B then weight S β J (ofEdgeFun S p) else 0 with hg
  set k : (↥S.edgeFinset → ℕ) → ℝ :=
    fun p => if sources S (ofEdgeFun S p) = C then weight S β J (ofEdgeFun S p) else 0 with hk
  set F : (Σ m : (↥S.edgeFinset → ℕ),
      {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}) → ℝ :=
    fun s => f s.2.1.1 * g s.2.1.2 * k (fun e => s.1 e - s.2.1.1 e - s.2.1.2 e) with hF
  have hgknorm : Summable
      (fun w : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) => ‖g w.1 * k w.2‖) := by
    apply ((summable_norm_currentSum_summand S β J B).mul_of_nonneg
      (summable_norm_currentSum_summand S β J C)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
    intro w; rw [norm_mul]
  have hABC := summable_mul_of_summable_norm (summable_norm_currentSum_summand S β J A) hgknorm
  have htriple : Summable
      (fun z : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) =>
        f z.1 * g z.2.1 * k z.2.2) := by
    have heq : (fun z : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) =>
        f z.1 * g z.2.1 * k z.2.2) = (fun z => f z.1 * (g z.2.1 * k z.2.2)) := by
      funext z; rw [mul_assoc]
    rw [heq]; exact hABC
  have hcomp : ∀ z : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ),
      f z.1 * g z.2.1 * k z.2.2 = F (tripleEquivSigma z) := by
    rintro ⟨p, q, r⟩
    simp only [hF, tripleEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => p e + q e + r e - p e - q e) = r := by ext e; omega
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (tripleEquivSigma (E := ↥S.edgeFinset)).summable_iff]
    exact htriple.congr (fun z => hcomp z)
  have hmarg : Summable (fun m : ↥S.edgeFinset → ℕ => ∑' K, F ⟨m, K⟩) := hsumF.sigma
  refine hmarg.congr (fun m => ?_)
  rw [tsum_fintype, ← gc15_inner_fiber_triple S β J m A B C]


theorem gc15_sourceTripleSum_eq_tFiber (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    sourceTripleSum S β J A B C = ∑' m, gc15_tFiber S β J A B C m := by
  rw [sourceTripleSum_eq_superposition]
  exact tsum_congr (fun m => gc15_inner_fiber_triple S β J m A B C)


end StatMech.Walls
