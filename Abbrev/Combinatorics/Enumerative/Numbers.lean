import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin


/-- Stirling numbers of the second kind (sympy `Stirling(n, k)`), realized by Mathlib's `Nat.stirlingSecond`. -/
abbrev Stirling (n k : ℕ) : ℕ := Nat.stirlingSecond n k

