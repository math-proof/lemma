/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part3


section

namespace MetaMathlibExt

open scoped BigOperators

noncomputable def encodeCell_aux (d n : ℕ) [NeZero n] (x : latticeCell d) :
    (Fin d → Fin n) :=
  fun k => ⟨(x k).toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩

end MetaMathlibExt
end
