import sympy.sets.sets
import sympy.Basic



@[main]
private lemma main
  {d : ℝ}
  {P : ℝ → Prop}
-- given
  (hd : 0 < d) :
-- imply
  (∀ x ∈ Ioo (-d) d, P x) ↔
    (∀ x ∈ Ioo (-d) 0, P x) ∧ (∀ x ∈ Ico 0 d, P x) := by
-- proof
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x ⟨hx.1, by linarith [hx.2]⟩
    · intro x hx
      exact h x ⟨by linarith [hd, hx.1], hx.2⟩
  · rintro ⟨h₁, h₂⟩ x hx
    by_cases h : 0 ≤ x
    · exact h₂ x ⟨h, hx.2⟩
    · exact h₁ x ⟨hx.1, by linarith⟩


-- created on 2023-10-22
