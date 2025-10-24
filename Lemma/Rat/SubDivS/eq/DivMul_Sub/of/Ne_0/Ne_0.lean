import Lemma.Rat.SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0
import Lemma.Int.Mul_Sub.eq.SubMulS
open Int Rat


@[main]
private lemma main
  [Field α]
  {x a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  x / a - x / b = x * (b - a) / (a * b) := by
-- proof
  have := SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0 (x := x) (y := x) h₀ h₁
  rwa [SubMulS.eq.Mul_Sub] at this


-- created on 2025-04-06
