/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part2

@[expose] public section

section

namespace MetaMathlibExt

open scoped BigOperators

def supportFinset_aux (d : ℕ) (S : Finset (latticeCell d)) : Finset (Fin d) :=
  Finset.univ.filter (fun k => ∃ x ∈ S, ∃ y ∈ S, x k ≠ y k)

end MetaMathlibExt
end
