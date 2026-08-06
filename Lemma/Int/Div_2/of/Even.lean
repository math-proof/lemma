import Lemma.Nat.Even.is.OddAdd_1
import Lemma.Nat.Div_2.of.Odd
import Lemma.Int.Div.eq.FloorDiv.of.Gt_0
import Lemma.Int.FDiv.eq.FloorDiv
open Nat Int


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n is even) :
-- imply
  n // 2 = (n + 1) // 2 := by
-- proof
  rw [FDiv.eq.FloorDiv (α := ℚ) n 2, FDiv.eq.FloorDiv (α := ℚ) (n + 1) 2]
  rw [← Div.eq.FloorDiv.of.Gt_0 (α := ℚ) (by decide), ← Div.eq.FloorDiv.of.Gt_0 (α := ℚ) (by decide)]
  simpa using Div_2.of.Odd (OddAdd_1.of.Even h)


-- created on 2026-08-06
