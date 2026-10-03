import Mathlib
import sympy.Basic

open Module

/--
[LinearMap_finrank_ker_dualMap_eq_finrank_ker](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_finrank_ker_dualMap_eq_finrank_ker.lean)
-/
@[main]
private lemma main
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {f : V →ₗ[K] V} :
-- imply
  finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f) := by
-- proof
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f)
  have h2 := f.finrank_range_add_finrank_ker
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  omega


-- created on 2026-10-03
