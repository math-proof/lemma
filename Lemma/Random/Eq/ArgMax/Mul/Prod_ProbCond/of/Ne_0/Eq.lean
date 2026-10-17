import sympy.Basic


/--
Equal scores have the same maximizers, so the argmax of a conditional probability and of its
Bayes rearrangement coincide.
-/
@[path]
private lemma main
  {f g : ι → ℝ}
  (i : ι)
-- given
  (h₀ : ∀ j, f j = g j) :
-- imply
  (∀ j, f j ≤ f i) ↔ (∀ j, g j ≤ g i) := by
-- proof
  simp [h₀]


-- created on 2026-10-11
-- updated on 2026-10-17
