import Lemma.Int.Eq_Neg.of.Add.eq.Zero
import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
open Int Rat


@[main]
private lemma main
  [Field α]
  {a b x : α}
-- given
  (h : a * x + b = 0) :
-- imply
  (a = 0 → b = 0) ∧ (a ≠ 0 → x = -b / a) := by
-- proof
  constructor
  ·
    intro ha
    simpa [ha] using h
  ·
    intro ha
    have hx : a * x = -b := Eq_Neg.of.Add.eq.Zero h
    exact Eq_Div.of.EqMul.Ne_0.left ha hx


-- created on 2018-08-16
-- updated on 2026-08-20
