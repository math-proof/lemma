import sympy.Basic
import Lemma.Rat.Div.lt.Zero.of.Lt_0
import Lemma.Int.LtMulS.of.Gt.Lt_0


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (hx : x < 0)
  (h : a > b) :
-- imply
  a / x < b / x := by
-- proof
  have hi : x⁻¹ < 0 := by
    have h1 := Rat.Div.lt.Zero.of.Lt_0 hx one_pos
    rwa [one_div] at h1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact Int.LtMulS.of.Gt.Lt_0 h hi


-- created on 2026-09-26
