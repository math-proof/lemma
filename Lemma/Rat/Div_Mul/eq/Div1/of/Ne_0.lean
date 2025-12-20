import Lemma.Rat.Div.eq.One.of.Ne_0
open Rat


@[main]
private lemma main
  [CommGroupWithZero α]
  {a : α}
-- given
  (h : a ≠ 0)
  (b : α) :
-- imply
  a / (a * b) = 1 / b := by
-- proof
  rw [div_mul_eq_div_mul_one_div]
  simp [Div.eq.One.of.Ne_0 h]


-- created on 2025-12-20
