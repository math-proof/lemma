import Lemma.Logic.OrOr.is.Or_Or
open Logic


@[main]
private lemma Comm :
-- imply
  a ∨ b ∨ c ↔ b ∨ a ∨ c := by
-- proof
  rw [Or_Or.is.OrOr]
  rw [Or.comm (b := b)]
  rw [OrOr.is.Or_Or]


-- created on 2025-06-06
