import sympy.functions.special.tensor_functions
import Lemma.Basic


@[main]
private lemma main
  [DecidableEq α]
  {g : ℕ → Prop}
  {x y : α}
-- given
  (h₀ : x = y)
  (h₁ : g 1) :
-- imply
  x = y ∧ g (KroneckerDelta x y) := by
-- proof
  rw [h₀]
  simpa [KroneckerDelta]


-- created on 2025-08-02
