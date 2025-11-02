import Lemma.Nat.Add
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
open Nat


@[main]
private lemma left
-- given
  (h : c > 0)
  (a b : ℕ) :
-- imply
  (c * a + b) / c = b / c + a := by
-- proof
  rw [DivAddMul.eq.Add_Div.of.Gt_0.left h]
  apply Add.comm


@[main]
private lemma main
-- given
  (h : c > 0)
  (a b : ℕ) :
-- imply
  (a * c + b) / c = b / c + a := by
-- proof
  rw [DivAddMul.eq.Add_Div.of.Gt_0 h]
  apply Add.comm


-- created on 2025-11-02
