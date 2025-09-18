import sympy.core.relational
import Lemma.Basic


@[main]
private lemma subst
  [Decidable p]
  {x : α}
  {f : α → β}
  {y : β} :
-- imply
  (if x = a ∧ p then
    f x
  else
    y) = if x = a ∧ p then
    f a
  else
    y := by
-- proof
  denote h_P : P = left
  rw [← h_P]


-- created on 2025-06-06
