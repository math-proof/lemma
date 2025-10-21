import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.Gt_0.of.Ne_0
open Nat


@[main]
private lemma left
-- given
  (h : c ≠ 0)
  (a b : ℕ) :
-- imply
  (c * a + b) / c = a + b / c :=
-- proof
  DivAddMul.eq.Add_Div.of.Gt_0.left (Gt_0.of.Ne_0 h) a b


@[main]
private lemma main
-- given
  (h : c ≠ 0)
  (a b : ℕ) :
-- imply
  (a * c + b) / c = a + b / c :=
-- proof
  DivAddMul.eq.Add_Div.of.Gt_0 (Gt_0.of.Ne_0 h) a b


-- created on 2025-10-21
