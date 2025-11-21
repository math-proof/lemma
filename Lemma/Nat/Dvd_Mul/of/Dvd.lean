import sympy.Basic


@[main]
private lemma main
  [CommSemigroup α]
  {y a : α}
-- given
  (h : a ∣ y)
  (x : α):
-- imply
  a ∣ x * y := by
-- proof
  apply dvd_mul_of_dvd_right h


@[main]
private lemma left
  [Semigroup α]
  {x a : α}
-- given
  (h : a ∣ x)
  (y : α) :
-- imply
  a ∣ x * y := by
-- proof
  apply dvd_mul_of_dvd_left h


-- created on 2025-07-08
