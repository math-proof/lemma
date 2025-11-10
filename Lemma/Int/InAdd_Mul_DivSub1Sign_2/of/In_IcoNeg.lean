import stdlib.Slice
import sympy.sets.sets
import Lemma.Int.DivSub1Sign_2.eq.Zero.of.Ge_0
import Lemma.Int.DivSub1Sign_2.eq.One.of.Lt_0
import Lemma.Int.Sub.ge.Zero.of.Ge
open Int


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
    if h_i : i ≥ 0 then
      have := DivSub1Sign_2.eq.Zero.of.Ge_0 h_i
      rw [this]
      simp_all
    else
      simp at h_i
      have := DivSub1Sign_2.eq.One.of.Lt_0 h_i
      rw [this]
      simp
      have := Sub.ge.Zero.of.Ge h_le
      simp at this
      assumption


-- created on 2025-06-26
