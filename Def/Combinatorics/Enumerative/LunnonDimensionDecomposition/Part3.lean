/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part2


section

namespace MetaMathlibExt

open scoped BigOperators

def supportFinset_aux (d : ℕ) (S : Finset (latticeCell d)) : Finset (Fin d) :=
  Finset.univ.filter (fun k => ∃ x ∈ S, ∃ y ∈ S, x k ≠ y k)

end MetaMathlibExt
end
