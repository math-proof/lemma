import Lemma.Bool.OrOr.is.Or_Or
open Bool


@[main]
private lemma comm' :
-- imply
  a ∨ b ∨ c ↔ b ∨ a ∨ c := by
-- proof
  rw [Or_Or.is.OrOr]
  rw [Or.comm (b := b)]
  rw [OrOr.is.Or_Or]


-- created on 2025-06-06
