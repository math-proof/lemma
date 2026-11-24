module
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Instance.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
section

namespace MetaMathlibExt

open scoped BigOperators

-- fiber over support A
def fiberSet_aux (d n : ℕ) (A : Finset (Fin d)) : Type :=
  { P : fixedPolycube d n // supportFinset_aux d P.val = A }

end MetaMathlibExt
end
