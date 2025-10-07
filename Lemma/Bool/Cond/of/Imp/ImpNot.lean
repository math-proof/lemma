import Lemma.Bool.Or_Not
open Bool


@[main]
private lemma main
  {p q : Prop}
-- given
  (h₀ : p → q)
  (h₁ : ¬p → q) :
-- imply
  q := by
-- proof
  cases Or_Not p with
  | inl hp =>
    -- Case 1: `hp` is a proof of `p`
    exact h₀ hp
  | inr hnp =>
    -- Case 2: `hnp` is a proof of `¬p`
    exact h₁ hnp


-- created on 2025-08-02
