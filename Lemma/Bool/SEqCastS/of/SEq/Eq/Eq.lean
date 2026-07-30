import Lemma.Bool.SEq.is.SEqCast.of.Eq
open Bool


@[main]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h₀ : n_a = n_a')
  (h₁ : n_b = n_b')
  (h₂ : a ≃ b) :
-- imply
  cast (congrArg Vector h₀) a ≃ cast (congrArg Vector h₁) b := by
-- proof
  apply SEqCast.of.SEq.Eq h₀
  apply SEq_Cast.of.SEq.Eq h₁ h₂


-- created on 2025-06-29
