import sympy.Basic


/--
Equal scores have the same minimizers.
-/
@[path]
private lemma main
  {f g : ι → ℝ}
  (i : ι)
-- given
  (h₀ : ∀ j, f j = g j) :
-- imply
  (∀ j, f i ≤ f j) ↔ (∀ j, g i ≤ g j) := by
-- proof
  simp [h₀]


-- created on 2021-07-21
-- updated on 2026-10-17
