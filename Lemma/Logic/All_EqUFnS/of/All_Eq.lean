import sympy.Basic


@[main]
private lemma list
  {s : List α}
  {a b : α → β}
  {f : β → γ}
-- given
  (h : ∀ i ∈ s, a i = b i) :
-- imply
  ∀ i ∈ s, f (a i) = f (b i) := by
-- proof
  intro i i_in_s
  rw [h i i_in_s]


@[main]
private lemma binary
  {s : Finset ι}
  {a b : ι → α}
  {f : α → ι → β}
-- given
  (h : ∀ i ∈ s, a i = b i) :
-- imply
  ∀ i ∈ s, f (a i) i = f (b i) i := by
-- proof
  intro i i_in_s
  rw [h i i_in_s]


@[main]
private lemma main
  {s : Finset α}
  {a b : α → β}
  {f : β → γ}
-- given
  (h : ∀ i ∈ s, a i = b i) :
-- imply
  ∀ i ∈ s, f (a i) = f (b i) := by
-- proof
  intro i i_in_s
  rw [h i i_in_s]


@[main]
private lemma is_constant
  {s : Finset ι}
  {x : ι → α}
  {f : α → β}
-- given
  (h : ∀ i ∈ s, x i = a) :
-- imply
  ∀ i ∈ s, f (x i) = f a := by
-- proof
  let b := fun _ : ι => a
  have := main (b := b) (f := f) h
  simp only [b] at this
  assumption


-- created on 2024-07-01
-- updated on 2025-04-26
