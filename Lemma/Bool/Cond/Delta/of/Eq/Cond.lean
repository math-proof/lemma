import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
open Nat


@[main]
private lemma main
  [DecidableEq α]
  {x y : α}
  {p : ℕ → Prop}
-- given
  (h₀ : x = y)
  (h₁ : p 1) :
-- imply
  p (KroneckerDelta x y) := by
-- proof
  rw [Delta.eq.Ite, if_pos h₀]
  exact h₁


-- created on 2019-02-26
