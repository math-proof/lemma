import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A : Finset α}
-- given
  (h₀ : A.card ≥ 1) :
-- imply
  A ≠ ∅ :=
-- proof
  (Finset.card_pos.mp h₀).ne_empty


-- created on 2021-04-09
-- updated on 2026-10-17
