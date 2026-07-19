import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Nat.Le.of.Lt
import Lemma.Rat.Gt0Div.of.Gt_0.Lt_0
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y < 0) :
-- imply
  x / y ≤ 0 := by
-- proof
  obtain hx | hx := Lt.ou.Eq.of.Le h₀
  ·
    apply Le.of.Lt
    apply Gt0Div.of.Gt_0.Lt_0 hx h₁
  ·
    simp [← hx]


-- created on 2025-11-07
