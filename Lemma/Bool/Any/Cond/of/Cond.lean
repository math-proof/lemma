import Lemma.Bool.Any.of.All
open Bool


@[path]
private lemma main
  {A : Set α}
  {f : α → Prop}
-- given
  (h₀ : A.Nonempty)
  (h₁ : ∀ e, f e) :
-- imply
  ∃ e ∈ A, f e := by
-- proof
  obtain ⟨e, he⟩ := h₀
  exact ⟨e, he, h₁ e⟩


-- created on 2019-03-17
