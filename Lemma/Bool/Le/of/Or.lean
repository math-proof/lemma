import sympy.Basic


@[path]
private lemma main
  [Preorder β]
  {A B : Set α} {x : α} [Decidable (x ∈ A)] [Decidable (x ∈ B)]
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
  obtain ⟨h₁, h₂⟩ | h₀ := h₀
  ·
    rwa [ite_eq_left h₂]
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h₀
  ·
    rwa [ite_eq_right h₂.2, ite_eq_left h₂.1]
  ·
    rwa [ite_eq_right (fun hA => h₂ (Or.inl hA)), ite_eq_right (fun hB => h₂ (Or.inr hB))]


@[path]
private lemma two
  [Preorder β]
  {A : Set α} {x : α} [Decidable (x ∈ A)]
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
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h₀
  ·
    rwa [ite_eq_left h₂]
  ·
    rwa [ite_eq_right h₂]


-- created on 2018-06-25
-- updated on 2026-10-12
