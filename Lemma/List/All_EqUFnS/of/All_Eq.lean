import sympy.Basic


@[main]
private lemma main
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


-- created on 2025-10-03
