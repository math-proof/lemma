import Lemma.Bool.Imp.is.Or_Not
open Bool


@[main]
private lemma main
  {p q : Prop}
-- given
  (h₀ : q ∨ ¬p)
  (h₁ : p) :
-- imply
  q := by
-- proof
  have := Imp.of.Or_Not h₀
  exact this h₁


-- created on 2025-04-12
