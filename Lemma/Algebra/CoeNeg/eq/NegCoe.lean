import sympy.Basic


@[main]
private lemma main
  [AddGroupWithOne R]
-- given
  (n : ℤ) :
-- imply
  ((-n : ℤ) : R) = -n :=
-- proof
  Int.cast_neg n


-- created on 2025-03-30
