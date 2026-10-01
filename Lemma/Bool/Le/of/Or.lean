import sympy.Basic


@[main]
private lemma main
  [Preorder β]
  {A B : Set α}
  {x : α}
  [Decidable (x ∈ A)] [Decidable (x ∈ B)]
  {f g k : α → β}
  {p : β}
-- given
  (h₀ : (f x ≤ p ∧ x ∈ A) ∨ (g x ≤ p ∧ x ∈ B \ A) ∨ (k x ≤ p ∧ x ∉ A ∪ B)) :
-- imply
  (if x ∈ A then
    f x
  else if x ∈ B then
    g x
  else
    k x) ≤ p := by
-- proof
  rcases h₀ with ⟨h₁, h₂⟩ | h₀
  ·
    rw [if_pos h₂]
    exact h₁
  rcases h₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  ·
    rw [if_neg h₂.2, if_pos h₂.1]
    exact h₁
  ·
    rw [if_neg (fun hA => h₂ (Or.inl hA)), if_neg (fun hB => h₂ (Or.inr hB))]
    exact h₁


@[main]
private lemma two
  [Preorder β]
  {A : Set α}
  {x : α}
  [Decidable (x ∈ A)]
  {f g : α → β}
  {p : β}
-- given
  (h₀ : (f x ≤ p ∧ x ∈ A) ∨ (g x ≤ p ∧ x ∉ A)) :
-- imply
  (if x ∈ A then
    f x
  else
    g x) ≤ p := by
-- proof
  rcases h₀ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  ·
    rw [if_pos h₂]
    exact h₁
  ·
    rw [if_neg h₂]
    exact h₁


-- created on 2026-09-27
