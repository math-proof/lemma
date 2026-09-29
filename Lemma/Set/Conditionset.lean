import sympy.Basic


@[main]
private lemma rewrite.domain_defined
  {n : ℕ}
  {x : Fin n → ℝ}
  {f : ℝ → ℝ} :
-- imply
  {i : ℕ | ∃ h : i < n, f (x ⟨i, h⟩) > 0} = {i : ℕ | i < n ∧ ∃ h : i < n, f (x ⟨i, h⟩) > 0} := by
-- proof
  ext i
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨h, hf⟩ => ⟨h, h, hf⟩, fun ⟨_, h⟩ => h⟩


-- created on 2026-09-27
