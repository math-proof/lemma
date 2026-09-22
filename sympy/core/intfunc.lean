import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Integer functions
[`sympy.core.intfunc`](https://github.com/sympy/sympy/blob/master/sympy/core/intfunc.py)
(home of multi-argument integer `igcd`).

`FiniteGCDOne` packages the number-theoretic condition that a set of naturals
contains a finite nonempty subset (excluding 0) whose GCD is 1 — the same
integer-GCD setting as SymPy `igcd(*args) = 1`.
-/
class FiniteGCDOne (A : Set ℕ) : Prop where
  finite_gcd_one : ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ A ∧ s.gcd id = 1 ∧ 0 ∉ s ∧ s.Nonempty
