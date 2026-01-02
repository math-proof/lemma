import stdlib.SEq
import Lemma.Bool.SEq.is.Eq
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
  apply Eq.of.SEq
  apply h₀.trans h₁


-- created on 2025-10-10
