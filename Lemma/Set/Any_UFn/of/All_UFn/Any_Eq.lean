import Lemma.Bool.Any_UFn.of.All_UFn.Any_Eq
open Bool


@[main]
private lemma main
  {a b : α → β}
  {p : β → Prop}
  {S : Set α}
-- given
  (h₀ : ∀ x ∈ S, p (a x))
  (h₁ : ∃ x ∈ S, a x = b x) :
-- imply
  ∃ x ∈ S, p (b x) := by
-- proof
  apply Any_UFn.of.All_UFn.Any_Eq h₀ h₁


-- created on 2018-12-24
-- updated on 2026-09-07
