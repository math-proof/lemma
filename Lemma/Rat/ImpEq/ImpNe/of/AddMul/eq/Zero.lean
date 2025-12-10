import Lemma.Int.Eq_Neg.of.Add.eq.Zero
import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
open Int Rat


@[main]
private lemma main
  [Field α]
  {x a b : α}
-- given
  (h : a * x + b = 0) :
-- imply
  (a = 0 → b = 0) ∧ (a ≠ 0 → x = -b / a) := by
-- proof
  constructor <;>
    intro ha
  ·
    rw [ha] at h
    simp_all
  ·
    apply Eq_Div.of.EqMul.Ne_0.left ha
    apply Eq_Neg.of.Add.eq.Zero h


-- created on 2024-07-01
-- updated on 2025-12-10
