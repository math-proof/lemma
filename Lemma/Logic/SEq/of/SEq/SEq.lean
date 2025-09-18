import stdlib.SEq
import Lemma.Basic


@[main]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n₀}
  {b : Vector n₁}
  {c : Vector n₂}
-- given
  (h₀ : a ≃ c)
  (h₁ : b ≃ c) :
-- imply
  a ≃ b :=
-- proof
  h₀.trans h₁.symm


-- created on 2025-04-20
-- updated on 2025-05-31
