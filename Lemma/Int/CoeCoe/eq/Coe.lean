import sympy.Basic


@[main, comm]
private lemma main
  [AddGroupWithOne R]
-- given
  (n : ℕ) :
-- imply
  ((n : ℤ) : R) = n :=
-- proof
  Int.cast_natCast n


-- created on 2025-09-30
-- updated on 2025-10-14
