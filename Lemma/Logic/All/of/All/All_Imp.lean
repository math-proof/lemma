import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma binary
  {s : Finset ι}
  {x : ι → α}
  {p q : α → ι → Prop}
-- given
  (h₀ : ∀ (t : α) (i : ι), p t i → q t i)
  (h₁ : ∀ i ∈ s, p (x i) i) :
-- imply
  ∀ i ∈ s, q (x i) i := by
-- proof
  -- Introduce the universal quantifier and the assumption that i is in the range n
  intro i hi
  -- Provide the proof of p (x i) using h₀ with the given index i and its range membership hi
  have := h₁ i hi
  -- Apply the implication h₁ to transform the goal into proving p (x i)
  apply h₀ (x i) i this


@[main]
private lemma fin
  {s : Finset ι}
  {x : ι → α}
  {p q : α → Prop}
-- given
  (h₀ : ∀ t : α, p t → q t)
  (h₁ : ∀ i ∈ s, p (x i)) :
-- imply
  ∀ i ∈ s, q (x i) := by
-- proof
  -- Introduce the universal quantifier and the assumption that i is in the range n
  intro i hi
  -- Provide the proof of p (x i) using h₀ with the given index i and its range membership hi
  have := h₁ i hi
  -- Apply the implication h₁ to transform the goal into proving p (x i)
  apply h₀ (x i) this


@[main]
private lemma main
  {x : ι → α}
  {p q : α → Prop}
-- given
  (h₀ : ∀ t : α, p t → q t)
  (h₁ : ∀ i : ι, p (x i)) :
-- imply
  ∀ i : ι, q (x i) := by
-- proof
  -- Introduce the universal quantifier and the assumption that i is in the range n
  intro i
  -- Provide the proof of p (x i) using h₀ with the given index i and its range membership hi
  have := h₁ i
  -- Apply the implication h₁ to transform the goal into proving p (x i)
  apply h₀ (x i) this


-- created on 2025-04-06
-- updated on 2025-04-26
