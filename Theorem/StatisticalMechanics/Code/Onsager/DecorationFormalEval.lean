/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEvalAlgebra.Part3


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_tsum_finite_exponent_buckets
    {I E : Type*} [Fintype I] [DecidableEq E]
    (exponent : I → E) (scalar : I → ℂ) (value : E → ℂ) :
    (∑' m : E,
      (∑ i : I, if exponent i = m then scalar i else 0) * value m) =
      ∑ i : I, scalar i * value (exponent i) := by
  classical
  let S : Finset E := Finset.univ.image exponent
  rw [tsum_eq_sum (s := S)]
  · calc
      (∑ m ∈ S,
          (∑ i : I, if exponent i = m then scalar i else 0) * value m) =
          ∑ m ∈ S, ∑ i : I,
            (if exponent i = m then scalar i else 0) * value m := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.sum_mul]
      _ = ∑ i : I, ∑ m ∈ S,
            (if exponent i = m then scalar i else 0) * value m := by
              rw [Finset.sum_comm]
      _ = ∑ i : I, scalar i * value (exponent i) := by
              apply Finset.sum_congr rfl
              intro i hi
              calc
                (∑ m ∈ S,
                    (if exponent i = m then scalar i else 0) * value m) =
                    (if exponent i = exponent i then scalar i else 0) *
                      value (exponent i) := by
                        apply Finset.sum_eq_single (exponent i)
                        · intro m hm hne
                          rw [if_neg (Ne.symm hne), zero_mul]
                        · simp [S]
                _ = scalar i * value (exponent i) := by simp
  · intro m hm
    have hnone : ∀ i : I, exponent i ≠ m := by
      intro i heq
      apply hm
      simp [S, ← heq]
    simp [hnone]

theorem ons_decFormalBucket_eval_eq_loopSum
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    (decWeight : ons_DecEdge L → ℂ) (r : ℕ) :
    (∑' m : ons_DecEdge L →₀ ℕ,
      (∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d
        else 0) *
        m.prod (fun edge n ↦ decWeight edge ^ n)) =
      ∑ d : Fin (r + 1) → ons_Dart L,
        ons_loopWeight
          (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d := by
  rw [ons_tsum_finite_exponent_buckets]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ons_loopWeight_KWmatDecorationWeightedPhase]

theorem ons_decFormalBucket_eval_div_eq_loopSum
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    (decWeight : ons_DecEdge L → ℂ) (r : ℕ) :
    (∑' m : ons_DecEdge L →₀ ℕ,
      ((∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d
        else 0) / ((r : ℂ) + 1)) *
        m.prod (fun edge n ↦ decWeight edge ^ n)) =
      (∑ d : Fin (r + 1) → ons_Dart L,
        ons_loopWeight
          (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d) /
        ((r : ℂ) + 1) := by
  rw [← ons_decFormalBucket_eval_eq_loopSum L omega u v decWeight r]
  rw [← tsum_div_const]
  apply tsum_congr
  intro m
  ring

theorem ons_tsum_finite_exponent_buckets_real
    {I E : Type*} [Fintype I] [DecidableEq E]
    (exponent : I → E) (scalar : I → ℝ) :
    (∑' m : E, ∑ i : I,
      if exponent i = m then scalar i else 0) = ∑ i : I, scalar i := by
  classical
  let S : Finset E := Finset.univ.image exponent
  rw [tsum_eq_sum (s := S)]
  · calc
      (∑ m ∈ S, ∑ i : I,
          if exponent i = m then scalar i else 0) =
          ∑ i : I, ∑ m ∈ S,
            if exponent i = m then scalar i else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ i : I, scalar i := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (∑ m ∈ S, if exponent i = m then scalar i else 0) =
              (if exponent i = exponent i then scalar i else 0) := by
            apply Finset.sum_eq_single (exponent i)
            · intro m hm hne
              rw [if_neg (Ne.symm hne)]
            · simp [S]
          _ = scalar i := by simp
  · intro m hm
    have hnone : ∀ i : I, exponent i ≠ m := by
      intro i heq
      apply hm
      simp [S, ← heq]
    simp [hnone]

end StatMech.Onsager
