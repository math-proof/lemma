import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Algebra.Add
open Algebra


@[main]
private lemma main
  {x a b : ℕ}
-- given
  (h₀ : x - b = a)
  (h₁ : b ≤ x) :
-- imply
  x = a + b := by
-- proof
  rw [← h₀]
  rw [EqAddSub.of.Ge]
  have : a ≥ 0 := by simp
  assumption


@[main]
private lemma left
  {x a b : ℕ}
-- given
  (h₀ : x - a = b)
  (h₁ : a ≤ x) :
-- imply
  x = a + b := by
-- proof
  rw [Add.comm]
  apply main h₀ h₁


-- created on 2025-03-31
