import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  [Preorder α] [Zero α]
  {d : ℝ}
  {f : ℝ → α}
-- given
  (h₀ : ∀ x ∈ Set.Ico 0 d, 0 < f x)
  (h₁ : ∀ x ∈ Set.Ioc (-d) 0, 0 < f x) :
-- imply
  ∀ x ∈ Set.Ioo (-d) d, 0 < f x := by
-- proof
  intro x hx
  obtain h | h := le_or_gt x 0
  ·
    exact h₁ x ⟨hx.1, h⟩
  ·
    exact h₀ x ⟨le_of_lt h, hx.2⟩


-- created on 2026-09-26
