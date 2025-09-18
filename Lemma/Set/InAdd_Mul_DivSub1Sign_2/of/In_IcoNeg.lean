import stdlib.Slice
import sympy.sets.sets
import Lemma.Algebra.DivSub1Sign_2.eq.Zero.of.Ge_0
import Lemma.Algebra.DivSub1Sign_2.eq.One.of.Lt_0
import Lemma.Algebra.Sub.ge.Zero.of.Ge
open Algebra


@[main]
private lemma main
  {i : ℤ}
  {n : ℕ}
-- given
  (h : i ∈ Ico (-n : ℤ) n) :
-- imply
  Slice.Add_Mul_DivSub1Sign_2 n i ∈ Ico (0 : ℤ) n := by
-- proof
  let ⟨h_le, h_lt⟩ := h
  constructor <;>
  ·
    unfold Slice.Add_Mul_DivSub1Sign_2
    by_cases h_i : i ≥ 0
    ·
      have := DivSub1Sign_2.eq.Zero.of.Ge_0 h_i
      rw [this]
      simp_all
    ·
      simp at h_i
      have := DivSub1Sign_2.eq.One.of.Lt_0 h_i
      rw [this]
      simp
      have := Sub.ge.Zero.of.Ge h_le
      simp at this
      assumption


-- created on 2025-06-26
