import Lemma.Algebra.Eq.ou.Gt.of.Ge
import Lemma.Nat.Le.of.Lt
import Lemma.Nat.Lt_0.of.Gt_0.Lt_0
open Algebra Nat


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y < 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  obtain hx | hx' := Eq.ou.Gt.of.Ge h₀
  ·
    simp_all
  ·
    apply Le.of.Lt
    apply Lt_0.of.Gt_0.Lt_0 hx' h₁


-- created on 2025-03-23
-- updated on 2025-04-04
