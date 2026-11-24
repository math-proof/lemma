module
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Instance.Combinatorics.Enumerative.LunnonDimensionDecomposition


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
section

namespace MetaMathlibExt

open scoped BigOperators

noncomputable def compressCell_aux2 (d : ℕ) (A : Finset (Fin d))
    (x : latticeCell d) : latticeCell A.card :=
  fun i => x ((Finset.orderIsoOfFin A rfl i : ↥A).val)

noncomputable def expandCell_aux2 (d : ℕ) (A : Finset (Fin d))
    (y : latticeCell A.card) : latticeCell d :=
  fun k => if h : k ∈ A then y ((Finset.orderIsoOfFin A rfl).symm ⟨k, h⟩) else 0

end MetaMathlibExt
end
