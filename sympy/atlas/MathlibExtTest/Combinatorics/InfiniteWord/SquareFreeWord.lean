/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/SquareFreeWord.lean -/


import sympy.atlas.Combinatorics.InfiniteWord.SquareFreeWord
import Lemma.Finset.InfiniteWord.SquareFreeWord

namespace MetaMathlibExt

example : IsWordSquare ([1, 2, 1, 2] : List ℕ) := by
  exact ⟨[1, 2], by simp, rfl⟩

example {α : Type*} (u : ℕ → α) (h : IsInfiniteSquareFreeWord u) : u 0 ≠ u 1 := by
  obtain ⟨j, hj, hne⟩ := h 0 1 (by decide)
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
  simpa [hj0] using hne

end MetaMathlibExt
