import Lemma.Nat.Square.eq.Mul
import Lemma.Nat.EqDivMul.of.Ne_0
open Nat


@[main]
private lemma main
  [GroupWithZero α]
  {x : α} :
-- imply
  x² / x = x := by
-- proof
  rw [Square.eq.Mul]
  by_cases h : x = 0
  ·
    rw [h]
    norm_num
  ·
    rw [EqDivMul.of.Ne_0 h]


-- created on 2025-04-06
