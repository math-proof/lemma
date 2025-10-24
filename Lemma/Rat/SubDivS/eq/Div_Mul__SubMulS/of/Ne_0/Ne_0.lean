import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.DivSub.eq.SubDivS
import Lemma.Rat.DivMul.eq.Mul_Div
import Lemma.Rat.Div_Mul.eq.Inv.of.Ne_0
open Algebra Rat


@[main]
private lemma main
  [Field α]
  {a b x y : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  x / a - y / b = (x * b - y * a) / (a * b) := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2025-03-01
