import Lemma.Int.Eq_Neg.of.Add.eq.Zero
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Rat.Eq_Div.of.Ne_0.EqMul
open Int Nat Rat


@[main]
private lemma main
  [Field α]
  {x a b : α}
-- given
  (h : a * x + b = 0) :
-- imply
  (a = 0 → b = 0) ∧
  (a ≠ 0 → x = -b / a) := by
-- proof
  constructor
  -- case left
  intro ha
  rw [ha] at h
  simp at h
  exact h
  -- case right
  intro ha
  have h: a * x = -b := Eq_Neg.of.Add.eq.Zero h
  have h: x = -b / a := Eq_Div.of.Ne_0.EqMul (left := true) ha h
  exact h


-- created on 2024-07-01
