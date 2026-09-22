import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic

/-!
# Set addition handlers
[`sympy.sets.handlers.add`](https://github.com/sympy/sympy/blob/master/sympy/sets/handlers/add.py)
(set addition / Minkowski-style handlers).

Note: SymPy `Set.is_closed` is **topological** closedness, not closure under
addition. The class below is the algebraic property `a, b ∈ A ⇒ a + b ∈ A`
on `Set ℕ` (no direct SymPy class; nearest module is this handlers path).
-/

/-- Algebraic closure of `A : Set ℕ` under addition. -/
class ClosedUnderAdd (A : Set ℕ) : Prop where
  closed_under_add : ∀ ⦃a b⦄, a ∈ A → b ∈ A → a + b ∈ A
