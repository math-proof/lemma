import Lemma.Nat.Lt.ou.Eq.ou.Gt
import Lemma.Nat.LtPowS.of.Lt.Gt_1
open Nat


@[main]
private lemma main
  [MonoidWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulStrictMono α]
  [MulPosStrictMono α]
  {x : α}
-- given
  (h₀ : x > 1)
  (h₁ : x ^ n = x ^ m) :
-- imply
  n = m := by
-- proof
  rcases Lt.ou.Eq.ou.Gt n m with h_lt | h_eq | h_gt
  ·
    have := LtPowS.of.Lt.Gt_1 h₀ h_lt
    aesop
  ·
    assumption
  ·
    have := LtPowS.of.Lt.Gt_1 h₀ h_gt
    aesop


-- created on 2025-05-23
