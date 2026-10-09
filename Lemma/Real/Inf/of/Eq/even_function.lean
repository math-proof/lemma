import sympy.sets.sets
import sympy.Basic


open scoped Pointwise


@[path]
private lemma main
  {f : ℝ → ℝ}
  {S : Set ℝ}
-- given
  (h : ∀ x, f x = f (-x)) :
-- imply
  sInf (f '' (-S)) = sInf (f '' S) := by
-- proof
  have himg : f '' (-S) = f '' S := by
    ext z
    constructor
    ·
      rintro ⟨x, hx, rfl⟩
      exact ⟨-x, Set.mem_neg.mp hx, by simp [← h]⟩
    ·
      rintro ⟨x, hx, rfl⟩
      exact ⟨-x, by simp [hx], by simp [← h]⟩
  rw [himg]


-- created on 2019-04-08
