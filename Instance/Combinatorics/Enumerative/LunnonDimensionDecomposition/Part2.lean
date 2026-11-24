module
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
section

namespace MetaMathlibExt

open scoped BigOperators

instance subsingleton_cell_zero_aux : Subsingleton (latticeCell 0) := by
  constructor
  intro x y
  funext k
  exact Fin.elim0 k

instance latticeCellDecEq_aux (d : ℕ) : DecidableEq (latticeCell d) :=
  inferInstanceAs (DecidableEq (Fin d → ℤ))

end MetaMathlibExt
end
