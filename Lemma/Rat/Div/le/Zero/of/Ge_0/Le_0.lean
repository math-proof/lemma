import Lemma.Nat.Eq.ou.Gt.of.Ge
import Lemma.Rat.Div.le.Zero.of.Ge_0.Lt_0
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y ≤ 0) :
-- imply
  x / y ≤ 0 := by
-- proof
  obtain hy | hy := Eq.ou.Gt.of.Ge h₁
  ·
    simp [← hy]
  ·
    apply Div.le.Zero.of.Ge_0.Lt_0 h₀ hy


-- created on 2025-11-07
