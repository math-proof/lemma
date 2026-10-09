import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h : sInf (f '' S) ≤ M₀) :
-- imply
  ∀ M > M₀, ∃ x ∈ S, f x < M := by
-- proof
  intro M hM
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := exists_lt_of_csInf_lt (h₀.image f) (lt_of_le_of_lt h hM)
  exact ⟨x, hx, hy⟩


-- created on 2019-04-06
