import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.LtMod.of.Gt_0
open Nat


@[main]
private lemma main
  {n d : ℕ}
-- given
  (h : n < d) :
-- imply
  n % d < d :=
-- proof
  (LtMod.of.Gt_0 ∘ Gt_0.of.Gt) h _


-- created on 2026-07-13
