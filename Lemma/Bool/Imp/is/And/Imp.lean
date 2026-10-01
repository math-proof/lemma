import sympy.Basic


@[main]
private lemma split
  {p q c : Prop} :
-- imply
  (p → q) ↔ (p ∧ c → q) ∧ (p ∧ ¬c → q) := by
-- proof
  constructor
  ·
    intro h
    exact ⟨fun hpc => h hpc.1, fun hpc => h hpc.1⟩
  ·
    rintro ⟨h₁, h₂⟩ hp
    by_cases hc : c
    ·
      exact h₁ ⟨hp, hc⟩
    ·
      exact h₂ ⟨hp, hc⟩


-- created on 2026-09-27
