import Lemma.Bool.Or.Any.of.Any
open Bool


@[main]
private lemma split
  {A : Set α}
  {f c : α → Prop} :
-- imply
  (∃ x ∈ A, f x) ↔ (∃ x ∈ A ∩ {x | c x}, f x) ∨ ∃ x ∈ A \ {x | c x}, f x := by
-- proof
  refine ⟨Or.Any.of.Any.split, ?_⟩
  rintro (⟨x, hx, hf⟩ | ⟨x, hx, hf⟩)
  ·
    exact ⟨x, hx.1, hf⟩
  ·
    exact ⟨x, hx.1, hf⟩


-- created on 2026-09-27
