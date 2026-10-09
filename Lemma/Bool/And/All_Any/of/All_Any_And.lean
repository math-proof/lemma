import Lemma.Bool.All.Any.of.All_Any_And
open Bool


@[path]
private lemma main
  {A : Set α}
  {B : Set β}
  {C : Set γ}
  {p q : α → β → γ → Prop}
-- given
  (h : ∀ x ∈ A, ∃ y ∈ B, ∀ z ∈ C, p x y z ∧ q x y z) :
-- imply
  (∀ x ∈ A, ∃ y ∈ B, ∀ z ∈ C, p x y z) ∧ ∀ x ∈ A, ∃ y ∈ B, ∀ z ∈ C, q x y z := by
-- proof
  refine ⟨All.Any.of.All_Any_And h, fun x hx => ?_⟩
  obtain ⟨y, hy, hz⟩ := h x hx
  exact ⟨y, hy, fun z hzC => (hz z hzC).2⟩


-- created on 2018-12-26
