import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Mul
open Nat


@[main]
private lemma main
  {n d a : ℕ}
-- given
  (h : a ≠ 0) :
-- imply
  (n * a) / (d * a) = n / d := by
-- proof
  rw [Mul.comm d a]
  rw [Div_Mul.eq.DivDiv]
  rw [EqDivMul.of.Ne_0 h]


@[main]
private lemma left
  {a n d : ℕ}
-- given
  (h : a ≠ 0) :
-- imply
  (a * n) / (a * d) = n / d := by
-- proof
  repeat rw [Mul.comm (a := a)]
  apply main h


-- created on 2026-07-12
