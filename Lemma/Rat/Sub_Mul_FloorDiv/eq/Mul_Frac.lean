import Lemma.Rat.Frac.eq.Sub_Floor
import Lemma.Rat.EqMulDiv.of.Gt_0
open Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {d : α}
-- given
  (h : d > 0)
  (n : α) :
-- imply
  n - d * ⌊n / d⌋ = d * fract (n / d) := by
-- proof
  rw [Frac.eq.Sub_Floor (x := n / d), mul_sub]
  congr 1
  rw [← mul_comm, EqMulDiv.of.Gt_0 h n]


-- created on 2026-08-03
