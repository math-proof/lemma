import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  x ≤ y ∧ x ≥ y := by
-- proof
  rw [h]
  exact ⟨le_refl y, le_refl y⟩


-- created on 2019-03-30
