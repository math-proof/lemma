/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Instance.Combinatorics.Enumerative.LunnonDimensionDecomposition


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
