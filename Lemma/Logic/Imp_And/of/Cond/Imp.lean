import Lemma.Basic


@[main]
private lemma main
-- given
  (h₀ : r)
  (h₁ : p → q) :
-- imply
  p → r ∧ q := by
-- proof
  intro hp
  constructor
  · exact h₀
  · exact h₁ hp


-- created on 2025-07-20
