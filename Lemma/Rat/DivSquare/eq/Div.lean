import Lemma.Nat.Mul
import Lemma.Nat.Square.eq.Mul
import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
open Nat Rat


@[main]
private lemma main
  [DivisionSemiring α]
  {a b : α}
-- given
  (h : b ≠ 0) :
-- imply
  b² / (a * b) = b / a := by
-- proof
  simp [Square.eq.Mul]
  rw [DivMulS.eq.Div.of.Ne_0 h]


@[main]
private lemma left
  [Semifield α]
  {a b : α}
-- given
  (h : a ≠ 0) :
-- imply
  a² / (a * b) = a / b := by
-- proof
  rw [Mul.comm (b := b)]
  apply main h


-- created on 2025-12-09
