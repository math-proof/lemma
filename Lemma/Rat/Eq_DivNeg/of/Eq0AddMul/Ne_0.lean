import Lemma.Int.Eq_Neg.of.Add.eq.Zero
import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
open Int Rat


@[main]
private lemma main
  [Field α]
  {a b x : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : a * x + b = 0) :
-- imply
  x = -b / a := by
-- proof
  apply Eq_Div.of.EqMul.Ne_0.left h₀
  apply Eq_Neg.of.Add.eq.Zero h₁


-- created on 2018-08-16
-- updated on 2026-08-22
