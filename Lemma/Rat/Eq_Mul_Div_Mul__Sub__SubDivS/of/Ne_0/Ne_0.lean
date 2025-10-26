import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Int.Mul_Sub.eq.SubMulS
import Lemma.Rat.Eq_Div_Mul__Sub__SubInvS.of.Ne_0.Ne_0
open Int Rat


@[main]
private lemma main
  [Field α]
  {x a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  x / a - x / b = x * ((b - a) / (a * b)) := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2025-03-01
