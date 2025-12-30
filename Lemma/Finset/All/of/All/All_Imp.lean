import sympy.Basic


@[main]
private lemma bin
  {s : Finset ι}
  {x : ι → α}
  {p q : α → ι → Prop}
-- given
  (h₀ : ∀ (t : α) (i : ι), p t i → q t i)
  (h₁ : ∀ i ∈ s, p (x i) i) :
-- imply
  ∀ i ∈ s, q (x i) i := by
-- proof
  intro i hi
  apply h₀ (x i) i
  apply h₁ i hi


@[main]
private lemma main
  {s : Finset ι}
  {x : ι → α}
  {p q : α → Prop}
-- given
  (h₀ : ∀ t : α, p t → q t)
  (h₁ : ∀ i ∈ s, p (x i)) :
-- imply
  ∀ i ∈ s, q (x i) := by
-- proof
  intro i hi
  apply h₀ (x i)
  apply h₁ i hi


-- created on 2025-12-30
