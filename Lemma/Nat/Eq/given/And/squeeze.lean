import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  x ≤ y ∧ x ≥ y := by
-- proof
  rw [h]
  exact ⟨le_refl y, le_refl y⟩


-- created on 2026-10-03
