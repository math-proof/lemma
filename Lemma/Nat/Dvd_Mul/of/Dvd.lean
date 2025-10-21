import sympy.Basic


@[main]
private lemma main
  [CommSemigroup α]
  {x y a : α}
-- given
  (h : a ∣ y) :
-- imply
  a ∣ x * y := by
-- proof
  apply dvd_mul_of_dvd_right h


@[main]
private lemma left
  [Semigroup α]
  {x y a : α}
-- given
  (h : a ∣ x) :
-- imply
  a ∣ x * y := by
-- proof
  apply dvd_mul_of_dvd_left h


-- created on 2025-07-08
