import Lemma.Nat.MulDiv.eq.Sub_Mod
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Le_Sub_1.of.Lt
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n d : Z}
-- given
  (h : d > 0) :
-- imply
  d * (n / d) ≥ n + 1 - d := by
-- proof
  rw [mul_comm, MulDiv.eq.Sub_Mod]
  rw [← IntegerRing.sub_pred h (n := n)]
  apply IntegerRing.sub_le_sub_left
  apply Le_Sub_1.of.Lt (LtMod.of.Gt_0 h n)


-- created on 2026-08-04
