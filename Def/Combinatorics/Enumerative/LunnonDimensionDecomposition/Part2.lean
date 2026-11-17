/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition

@[expose] public section

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
