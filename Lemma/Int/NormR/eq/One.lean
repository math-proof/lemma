import Mathlib
import sympy.Basic


/--
[Algebra_norm_of_subsingleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_norm_of_subsingleton.lean)
-/
@[main]
private lemma main
  [CommRing R] [Ring A] [Algebra R A] [Subsingleton A]
  {a : A} :
-- imply
  Algebra.norm R a = 1 :=
-- proof
  LinearMap.det_eq_one_of_subsingleton _


-- created on 2026-10-02
