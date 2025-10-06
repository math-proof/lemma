import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Algebra.Gt.of.Ge.Gt
open Algebra


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h₀ : y > 0)
  (h₁ : x ≤ y) :
-- imply
  x - 1 < y := by
-- proof
  apply Nat.lt_of_le_sub_one h₀
  apply Nat.le_of_succ_le_succ
  simp
  rwa [EqAddSub.of.Ge]
  linarith


@[main]
private lemma left
  {x y : ℕ}
-- given
  (h₀ : x > 0)
  (h₁ : x ≤ y) :
-- imply
  x - 1 < y := by
-- proof
  apply main _ h₁
  apply Gt.of.Ge.Gt h₁ h₀


-- created on 2025-05-03
-- updated on 2025-06-21
