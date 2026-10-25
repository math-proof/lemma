/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part7


section

namespace MetaMathlibExt

open scoped BigOperators

instance finite_fiber_aux (d n : ℕ) (A : Finset (Fin d)) :
    Finite (fiberSet_aux d n A) :=
  Finite.of_injective Subtype.val (fun _ _ h => Subtype.ext h)

end MetaMathlibExt
end
