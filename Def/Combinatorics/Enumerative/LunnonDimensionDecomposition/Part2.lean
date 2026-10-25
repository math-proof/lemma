/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition


section

namespace MetaMathlibExt

open scoped BigOperators

noncomputable def polyGraph_aux (d : ℕ) (S : Finset (latticeCell d)) : SimpleGraph ↥S :=
  SimpleGraph.mk
    (Adj := fun a b => faceAdjacent d (a : latticeCell d) (b : latticeCell d))
    (symm := Std.Symm.mk (fun _ _ h => by
      obtain ⟨k, hagree, hstep⟩ := h
      exact ⟨k, fun j hj => (hagree j
          hj).symm, by rcases hstep with h | h <;> [right; left] <;> omega⟩))
    (loopless := Std.Irrefl.mk (fun _ h => by
      obtain ⟨k, _, hstep⟩ := h
      rcases hstep with h | h <;> omega))

end MetaMathlibExt
end
