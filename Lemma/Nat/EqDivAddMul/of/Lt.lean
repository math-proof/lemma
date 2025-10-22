import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Ne_0
open Nat


@[main]
private lemma left
-- given
  (h : b < c)
  (a : ℕ) :
-- imply
  (c * a + b) / c = a := by
-- proof
  simp_all [DivAddMul.eq.Add_Div.of.Ne_0.left (show c ≠ 0 by omega)]


@[main]
private lemma main
-- given
  (h : b < c)
  (a : ℕ) :
-- imply
  (a * c + b) / c = a := by
-- proof
  simp_all [DivAddMul.eq.Add_Div.of.Ne_0 (show c ≠ 0 by omega)]


-- created on 2025-10-22
