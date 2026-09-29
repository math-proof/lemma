import sympy.Basic


@[main]
private lemma main
  [DecidableEq α] [DecidableEq β]
  {A : Finset α}
  {B : Finset β}
  {f : α → β}
  {g : β → α}
-- given
  (h₀ : B.image g = A)
  (h₁ : A.image f = B) :
-- imply
  A.card = B.card := by
-- proof
  have h_A := Finset.card_image_le (s := B) (f := g)
  have h_B := Finset.card_image_le (s := A) (f := f)
  rw [h₀] at h_A
  rw [h₁] at h_B
  omega


-- created on 2026-09-27
