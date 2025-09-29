import sympy.Basic


@[main]
private lemma main
  [Decidable f]
  [Decidable g]
-- given
  (s : Set α) :
-- imply
  (if f ∧ g then
    s
  else
    ∅) = (if f then
    s
  else
    ∅) ∩ if g then
    s
  else
    ∅ := by
-- proof
  aesop


-- created on 2025-08-03
