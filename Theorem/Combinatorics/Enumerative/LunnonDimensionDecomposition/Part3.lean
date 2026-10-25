/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part3


section

namespace MetaMathlibExt

open scoped BigOperators

lemma properDimension_eq_support_aux (d : ℕ) (S : Finset (latticeCell d)) :
    properDimension d S = (supportFinset_aux d S).card := by
  unfold properDimension supportFinset_aux
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]

end MetaMathlibExt
end
