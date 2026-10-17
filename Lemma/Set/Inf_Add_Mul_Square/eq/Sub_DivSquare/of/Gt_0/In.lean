import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c lo hi : ℝ}
-- given
  (h₀ : 0 < a)
  (h₁ : -b / (2 * a) ∈ Set.Icc lo hi) :
-- imply
  -b / (2 * a) ∈ Set.Icc lo hi ∧
    ∀ x ∈ Set.Icc lo hi, c - b ^ 2 / (4 * a) ≤ a * x ^ 2 + b * x + c := by
-- proof
  refine ⟨h₁, ?_⟩
  intro x _
  field_simp [h₀.ne']
  nlinarith [sq_nonneg (2 * a * x + b)]


-- created on 2026-10-11
-- updated on 2026-10-17
