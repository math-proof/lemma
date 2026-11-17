module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Fin
public import Abbrev.Combinatorics.Enumerative.Numbers

@[expose] public section

/-- sympy `Stirling.conditionset(n, k, x)`: ordered k-tuples of nonempty finite sets whose union is `range n` and whose cardinalities sum to `n` (i.e. ordered set partitions of `range n` into k blocks). -/
def Stirling.conditionset (n k : ℕ) : Set (Fin k → Finset ℕ) :=
  {x | Finset.univ.biUnion x = Finset.range n ∧ ∑ i, (x i).card = n ∧ ∀ i, 0 < (x i).card}

