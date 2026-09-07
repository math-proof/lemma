import Lemma.Bool.Any_And.of.Any.All
import Lemma.Bool.UFn.of.UFn.Eq
open Bool


@[main]
private lemma main
  {a b : α → β}
  {p : β → Prop}
  {r : α → Prop}
-- given
  (h₀ : ∀ x | r x, p (a x))
  (h₁ : ∃ x | r x, a x = b x) :
-- imply
  ∃ x | r x, p (b x) := by
-- proof
  have h := Any_And.of.Any.All h₀ h₁
  let ⟨x, hr, hp, heq⟩ := h
  use x, hr
  apply UFn.of.UFn.Eq heq hp


-- created on 2018-12-24
-- updated on 2026-09-07
