import Lemma.Real.OrEqS.of.Square
open Real


@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h : a ^ 2 = b ^ 2) :
-- imply
  a - b = 0 ∨ a + b = 0 := by
-- proof
  rcases OrEqS.of.Square h with h | h
  ·
    exact Or.inl (sub_eq_zero.mpr h)
  ·
    exact Or.inr (add_eq_zero_iff_eq_neg.mpr h)


-- created on 2018-11-13
-- updated on 2026-08-20
