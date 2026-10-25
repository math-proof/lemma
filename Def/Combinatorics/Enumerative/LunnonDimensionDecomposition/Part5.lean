/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part4


section

namespace MetaMathlibExt

open scoped BigOperators

noncomputable def encodeSet_aux (d n : ℕ) [NeZero n] (P : fixedPolycube d n) :
    Finset (Fin d → Fin n) :=
  Finset.image (encodeCell_aux d n) P.val

end MetaMathlibExt
end
