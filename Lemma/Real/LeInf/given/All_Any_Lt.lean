import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b M0 : ℝ}
  {f : ℝ → ℝ}
-- given
  (hne : (Set.Ioo a b).Nonempty)
  (h : sInf (f '' Set.Ioo a b) ≤ M0) :
-- imply
  ∀ M, M0 < M → ∃ x, x ∈ Set.Ioo a b ∧ f x < M := by
-- proof
  intro M hM
  obtain ⟨y, ⟨x, hx, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt (hne.image f) (lt_of_le_of_lt h hM)
  exact ⟨x, hx, hlt⟩


-- created on 2019-04-07
