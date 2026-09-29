import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

/-- Stirling numbers of the second kind (sympy `Stirling(n, k)`), realized by Mathlib's `Nat.stirlingSecond`. -/
abbrev Stirling (n k : ℕ) : ℕ := Nat.stirlingSecond n k

/-- sympy `Stirling.conditionset(n, k, x)`: ordered k-tuples of nonempty finite sets whose union is `range n` and whose cardinalities sum to `n` (i.e. ordered set partitions of `range n` into k blocks). -/
def Stirling.conditionset (n k : ℕ) : Set (Fin k → Finset ℕ) :=
  {x | Finset.univ.biUnion x = Finset.range n ∧ ∑ i, (x i).card = n ∧ ∀ i, 0 < (x i).card}
