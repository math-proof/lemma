import Lemma.Int.Div.eq.FloorDiv.of.Gt_0
import Lemma.Nat.Mul_Div.ge.SubAdd_1.of.Gt_0
open Nat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  d * ⌊(n : α) / (d : α)⌋ ≥ n + 1 - d := by
-- proof
  rw [← Div.eq.FloorDiv.of.Gt_0 (α := α) (n := (n : ℤ)) (d := (d : ℤ)) h]
  exact_mod_cast Mul_Div.ge.SubAdd_1.of.Gt_0 h


-- created on 2018-05-27
