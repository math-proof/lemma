import Lemma.Logic.SEqCast.of.SEq.Eq
open Logic


@[main]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h₀ : n = n')
  (h₁ : m = m')
  (h₂ : a ≃ b) :
-- imply
  have h : Vector n = Vector n' := by rw [h₀]
  have h' : Vector m = Vector m' := by rw [h₁]
  cast h a ≃ cast h' b := by
-- proof
  apply SEqCast.of.SEq.Eq h₀
  apply SEq_Cast.of.SEq.Eq h₁ h₂


-- created on 2025-06-29
