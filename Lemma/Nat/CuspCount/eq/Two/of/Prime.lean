import Mathlib
import sympy.Basic
import Lemma.ModularCurve.GenusNumerics
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_cuspCount_prime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_cuspCount_prime.lean)
-/
@[path]
private lemma main
  {p : ℕ}
-- given
  (hp : p.Prime) :
-- imply
  cuspCount p = 2 := by
-- proof
  rw [cuspCount, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  rw [Nat.div_one, Nat.div_self hp.pos]
  simp


-- created on 2026-10-23
