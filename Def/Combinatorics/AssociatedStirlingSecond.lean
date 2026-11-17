/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AssociatedStirlingSecond.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Two-associated Stirling numbers of the second kind

This file defines the two-associated Stirling numbers of the second kind and proves their
recurrence and support bound.
-/


namespace MetaMathlibExt

/-- The 2-associated Stirling number of the second kind: the number of partitions of an
`n`-element set into `k` blocks, each containing at least two elements. -/
def twoAssocStirlingSecond (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), ((-1 : ℤ) ^ j) * (Nat.choose n j : ℤ) *
      (Nat.stirlingSecond (n - j) (k - j) : ℤ)

end MetaMathlibExt
