import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
import sympy.Basic
open Nat


@[main]
private lemma main
  [DecidableEq α]
  {x y : α}
  {f : α → α → β}
  {g : ℕ → β}
-- given
  (h₀ : x = y)
  (h₁ : g 1 ≠ f x y) :
-- imply
  g (KroneckerDelta x y) ≠ f x y := by
-- proof
  rw [Delta.eq.Ite, if_pos h₀]
  exact h₁


-- created on 2026-10-03
