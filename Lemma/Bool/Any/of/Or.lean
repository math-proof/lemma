import Lemma.Bool.And.is.All.limits.Union
open Bool


@[path]
private lemma main
  {A B : Set α}
  {f : α → Prop}
-- given
  (h : (∃ x ∈ A, f x) ∨ ∃ x ∈ B, f x) :
-- imply
  ∃ x ∈ A ∪ B, f x := by
-- proof
  rcases h with ⟨x, hx, hf⟩ | ⟨x, hx, hf⟩
  ·
    exact ⟨x, Or.inl hx, hf⟩
  ·
    exact ⟨x, Or.inr hx, hf⟩


-- created on 2020-02-18
