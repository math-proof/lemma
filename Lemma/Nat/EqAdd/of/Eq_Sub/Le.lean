import Lemma.Nat.Eq_Add.of.EqSub.Le
import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {x a b : ℕ}
-- given
  (h₀ : a = x - b)
  (h₁ : b ≤ x) :
-- imply
  a + b = x := by
-- proof
  have h₀ := h₀.symm
  have := Eq_Add.of.EqSub.Le h₀ h₁
  exact this.symm


@[main]
private lemma left
  {x a b : ℕ}
-- given
  (h₀ : b = x - a)
  (h₁ : a ≤ x) :
-- imply
  a + b = x := by
-- proof
  rw [Add.comm]
  apply main h₀ h₁


-- created on 2025-03-31
