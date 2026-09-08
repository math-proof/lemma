import Lemma.Bool.All_UFn.of.UFn.All_Eq
open Bool


@[main]
private lemma main
  {a b : α → β}
  {p : α → β → Prop}
  {S : Set α}
-- given
  (h₀ : ∀ x ∈ S, a x = b x)
  (h₁ : ∀ x ∈ S, p x (a x)) :
-- imply
  ∀ x ∈ S, p x (b x) := by
-- proof
  apply All_UFn.of.UFn.All_Eq h₀ h₁


-- created on 2019-01-06
-- updated on 2026-09-08
