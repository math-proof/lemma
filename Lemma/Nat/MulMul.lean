import sympy.Basic


@[main]
private lemma Comm
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = a * c * b := by
-- proof
  grind


@[main]
private lemma swap
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = b * a * c := by
-- proof
  grind


@[main]
private lemma reverse
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = c * b * a := by
-- proof
  grind


@[main, comm]
private lemma rotate
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = b * c * a := by
-- proof
  grind


-- created on 2024-11-29
-- updated on 2026-07-31
