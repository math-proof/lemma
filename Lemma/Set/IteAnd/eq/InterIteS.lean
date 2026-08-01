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


-- created on 2018-09-25
