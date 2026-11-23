/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part3

@[expose] public section

section

namespace MetaMathlibExt

open scoped BigOperators

noncomputable def encodeCell_aux (d n : ℕ) [NeZero n] (x : latticeCell d) :
    (Fin d → Fin n) :=
  fun k => ⟨(x k).toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩

end MetaMathlibExt
end
