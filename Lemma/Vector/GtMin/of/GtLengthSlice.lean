import Lemma.Int.EqToNat
import Lemma.Int.EqToNat_0.of.Le_0
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Rat.Div.le.Zero.of.Le_0
open Int Nat Rat Slice


@[main]
private lemma main
  {a b d n : ℕ}
-- given
  (h : (⟨a, b, d⟩ : Slice).length n > 0) :
-- imply
  a < b ⊓ n := by
-- proof
  set stop := b ⊓ n
  by_contra h
  have h_toNat : ⌈((stop : ℚ) - a) / d⌉.toNat = 0 := by
    apply EqToNat_0.of.Le_0
    apply Int.ceil_nonpos.mpr
    simpa using Div.le.Zero.of.Le_0 (sub_nonpos.mpr (Nat.cast_le.mpr (le_of_not_gt h))) d
  have h_len_zero : (⟨a, b, d⟩ : Slice).length n = 0 := by
    unfold Slice.length
    simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat]
    grind
  grind


-- created on 2026-08-09
