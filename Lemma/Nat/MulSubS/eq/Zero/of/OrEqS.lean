import Lemma.Nat.Sub.eq.Zero
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
open Nat


@[main]
private lemma main
  [MulZeroClass α] [NoZeroDivisors α]
  [SubSelf α]
  {x y a b : α}
-- given
  (h : x = a ∨ y = b) :
-- imply
  (x - a) * (y - b) = 0 := by
-- proof
  apply Mul.eq.Zero.of.OrEqS_0
  obtain h₀ | h₁ := h
  ·
    subst h₀
    left
    apply Sub.eq.Zero
  ·
    subst h₁
    right
    apply Sub.eq.Zero


-- created on 2025-04-11
-- updated on 2025-10-16
