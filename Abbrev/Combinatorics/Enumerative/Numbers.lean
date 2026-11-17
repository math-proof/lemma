module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Fin

@[expose] public section


/-- Stirling numbers of the second kind (sympy `Stirling(n, k)`), realized by Mathlib's `Nat.stirlingSecond`. -/
abbrev Stirling (n k : ℕ) : ℕ := Nat.stirlingSecond n k

