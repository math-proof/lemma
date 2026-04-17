import sympy.Basic


@[main]
private lemma main
  [SemigroupWithZero α]
-- given
  (a : α) :
-- imply
  a ∣ 0 :=
-- proof
  dvd_zero a


-- created on 2026-04-16
