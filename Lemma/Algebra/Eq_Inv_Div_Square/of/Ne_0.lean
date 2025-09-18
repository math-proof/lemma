import Lemma.Algebra.Square.eq.Mul
import Lemma.Algebra.DivDiv.eq.Div_Mul
open Algebra


@[main]
private lemma main
  [Field α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / a² = a⁻¹ := by
-- proof
  rw [
    Square.eq.Mul,
    Div_Mul.eq.DivDiv
  ]
  simp [h]


-- created on 2024-07-01
