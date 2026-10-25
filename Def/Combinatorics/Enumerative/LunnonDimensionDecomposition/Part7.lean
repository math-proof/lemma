/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Instance.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part2


section

namespace MetaMathlibExt

open scoped BigOperators

-- fiber over support A
def fiberSet_aux (d n : ℕ) (A : Finset (Fin d)) : Type :=
  { P : fixedPolycube d n // supportFinset_aux d P.val = A }

end MetaMathlibExt
end
