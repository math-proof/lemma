/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part4

@[expose] public section

section

namespace MetaMathlibExt

open scoped BigOperators

noncomputable def encodeSet_aux (d n : ℕ) [NeZero n] (P : fixedPolycube d n) :
    Finset (Fin d → Fin n) :=
  Finset.image (encodeCell_aux d n) P.val

end MetaMathlibExt
end
