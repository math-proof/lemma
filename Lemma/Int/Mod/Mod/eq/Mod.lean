import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n d k : ℤ} :
-- imply
  n % (d * k) % d = n % d := by
-- proof
  exact Int.emod_emod_of_dvd n (dvd_mul_right d k)


-- created on 2026-09-27
