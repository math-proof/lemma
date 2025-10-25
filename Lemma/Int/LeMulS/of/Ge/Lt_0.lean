import Lemma.Int.LeMulS.of.Ge.Le_0
import Lemma.Nat.Le.of.Lt
open Nat Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x < 0) :
-- imply
  a * x ≤ b * x := by
-- proof
  apply LeMulS.of.Ge.Le_0 h₀
  apply Le.of.Lt h₁


-- created on 2025-03-23
-- updated on 2025-03-30
