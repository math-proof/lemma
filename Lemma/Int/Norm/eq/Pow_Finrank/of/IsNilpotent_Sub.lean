import Mathlib
import sympy.Basic


/--
[Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap.lean)
-/
@[main]
private lemma main
  {R A : Type*} [CommRing R] [IsDomain R] [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
  {a : A}
  {μ : R}
-- given
  (h : IsNilpotent (a - algebraMap R A μ)) :
-- imply
  Algebra.norm R a = μ ^ Module.finrank R A := by
-- proof
  have hN : IsNilpotent (Algebra.lmul R A (a - algebraMap R A μ)) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hN' : IsNilpotent (-(Algebra.lmul R A (a - algebraMap R A μ))) := hN.neg
  have hsplit : (Algebra.lmul R A) a
      = algebraMap R (Module.End R A) μ - (-(Algebra.lmul R A (a - algebraMap R A μ))) := by
    rw [sub_neg_eq_add, ← (Algebra.lmul R A).commutes μ, ← map_add]
    congr 1
    abel
  rw [Algebra.norm_apply, hsplit, ← LinearMap.eval_charpoly,
    IsNilpotent.charpoly_eq_X_pow_finrank hN', Polynomial.eval_pow, Polynomial.eval_X]


-- created on 2026-10-05
