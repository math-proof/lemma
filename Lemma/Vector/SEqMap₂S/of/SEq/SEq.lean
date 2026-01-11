import Lemma.Bool.SEq.is.Eq
open Bool


@[main]
private lemma main
  {a : List.Vector α n}
  {a' : List.Vector α n'}
  {b : List.Vector β n}
  {b' : List.Vector β n'}
-- given
  (h_a : a ≃ a')
  (h_b : b ≃ b')
  (f : α → β → γ) :
-- imply
  List.Vector.map₂ f a b ≃ List.Vector.map₂ f a' b' := by
-- proof
  have h_n : n = n' := h_a.left
  subst h_n
  have h_a := Eq.of.SEq h_a
  have h_b := Eq.of.SEq h_b
  subst h_a h_b
  rfl


-- created on 2026-01-11
