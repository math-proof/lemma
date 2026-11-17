/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition

public section

section

namespace MetaMathlibExt

open scoped BigOperators

lemma faceAdjacent_step_le_aux (d : ℕ) (x y : latticeCell d) (k : Fin d)
    (h : faceAdjacent d x y) : |x k - y k| ≤ 1 := by
  obtain ⟨k', hagree, hstep⟩ := h
  by_cases hk : k = k'
  · subst hk
    rcases hstep with h | h
    · rw [h]; simp
    · rw [h]; simp
  · rw [hagree k hk]; simp

end MetaMathlibExt
end
