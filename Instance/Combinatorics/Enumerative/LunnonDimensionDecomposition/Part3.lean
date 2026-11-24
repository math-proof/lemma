module
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
section

namespace MetaMathlibExt

open scoped BigOperators

instance finite_fiber_aux (d n : ℕ) (A : Finset (Fin d)) :
    Finite (fiberSet_aux d n A) :=
  Finite.of_injective Subtype.val (fun _ _ h => Subtype.ext h)

end MetaMathlibExt
end
