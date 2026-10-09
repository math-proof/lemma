import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b M0 : ℝ}
  {f : ℝ → ℝ}
-- given
  (hB : BddBelow (f '' Set.Ioo a b))
  (h : ∀ M, M ≥ M0 → ∃ x, x ∈ Set.Ioo a b ∧ f x < M) :
-- imply
  sInf (f '' Set.Ioo a b) ≤ M0 := by
-- proof
  obtain ⟨x, hx, hfx⟩ := h M0 (le_refl M0)
  exact le_trans (csInf_le hB (Set.mem_image_of_mem f hx)) hfx.le


-- created on 2026-10-03
