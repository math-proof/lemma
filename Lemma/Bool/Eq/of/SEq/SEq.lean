import stdlib.SEq
import Lemma.Bool.Eq.of.SEq
open Bool


@[main]
private lemma main
  {Vector : α → Sort v}
  {a c : Vector n}
  {b : Vector n'}
-- given
  (h₀ : a ≃ b)
  (h₁ : b ≃ c) :
-- imply
  a = c := by
-- proof
  apply Eq.of.SEq.simp
  apply SEq.trans h₀ h₁


-- created on 2025-10-10
