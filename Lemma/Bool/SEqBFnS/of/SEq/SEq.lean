import Lemma.Bool.SEq.is.Eq
open Bool


@[main]
private lemma main
  {Vector : N → Sort v}
  {a b : Vector n}
  {a' b' : Vector n'}
  {g : N → N}
-- given
  (h_a : a ≃ a')
  (h_b : b ≃ b')
  (f : {n : N} → Vector n → Vector n → Vector (g n)) :
-- imply
  f a b ≃ f a' b' := by
-- proof
  have h_s := h_a.left
  subst h_s
  have h_a := Eq.of.SEq h_a
  have h_b := Eq.of.SEq h_b
  subst h_a h_b
  rfl


-- created on 2026-07-11
