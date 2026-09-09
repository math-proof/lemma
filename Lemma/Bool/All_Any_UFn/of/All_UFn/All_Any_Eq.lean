import Lemma.Bool.Any_UFn.of.All_UFn.Any_Eq
open Bool


@[main]
private lemma main
  {a b : α → ι → β}
  {p : β → Prop}
  {r : α → Prop}
  {s : ι → Prop}
-- given
  (h₀ : ∀ y | s y, ∃ x | r x, a x y = b x y)
  (h₁ : ∀ y | s y, ∀ x | r x, p (a x y)) :
-- imply
  ∀ y | s y, ∃ x | r x, p (b x y) := by
-- proof
  intro y hy
  apply Any_UFn.of.All_UFn.Any_Eq (h₁ y hy) (h₀ y hy)


-- created on 2018-12-25
-- updated on 2026-09-09
