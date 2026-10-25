/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition


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
