import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
open Nat
@[main]
private lemma main
  [DecidableEq α]
  {x y : α}
  {p : ℕ → Prop}
-- given
  (h₀ : x ≠ y)
  (h₁ : p (KroneckerDelta x y)) :
-- imply
  p 0 := by
-- proof
  rw [Delta.eq.Ite, if_neg h₀] at h₁
  exact h₁
-- created on 2020-07-18
