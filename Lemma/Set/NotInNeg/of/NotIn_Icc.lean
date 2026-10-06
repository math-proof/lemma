import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h : x ∉ Set.Icc a b) :
-- imply
  -x ∉ Set.Icc (-b) (-a) := by
-- proof
  intro hmem
  obtain ⟨h₁, h₂⟩ := hmem
  rw [neg_le_neg_iff] at h₁ h₂
  exact h ⟨h₂, h₁⟩


-- created on 2018-06-19
