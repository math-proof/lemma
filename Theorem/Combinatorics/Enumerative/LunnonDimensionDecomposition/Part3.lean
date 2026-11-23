/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part3

public section

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
