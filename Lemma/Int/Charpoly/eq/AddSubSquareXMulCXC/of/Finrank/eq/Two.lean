import Mathlib
import sympy.Basic

open Polynomial

/--
[LinearMap_charpoly_of_finrank_eq_two](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_charpoly_of_finrank_eq_two.lean)
-/
@[path]
private lemma main
  [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  {f : M →ₗ[R] M}
-- given
  (h : Module.finrank R M = 2) :
-- imply
  f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f) := by
-- proof
  let b := Module.finBasisOfFinrankEq R M h
  rw [← f.charpoly_toMatrix b, Matrix.charpoly_fin_two, ← LinearMap.trace_eq_matrix_trace R b f,
    LinearMap.det_toMatrix b f]


-- created on 2026-10-03
