import Mathlib
import sympy.Basic


/--
[LinearMap_trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two.lean)
-/
@[main]
private lemma main
  [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {Φ : V →ₗ[k] V}
  {t n : k}
-- given
  (hV : Module.finrank k V = 2)
  (hΦ : Φ * Φ - t • Φ + n • (1 : V →ₗ[k] V) = 0) :
-- imply
  (LinearMap.trace k V Φ - t) * ((LinearMap.trace k V Φ - t) ^ 2 - (t ^ 2 - 4 * n)) = 0 := by
-- proof
  classical

  let b := Module.finBasisOfFinrankEq k V hV
  set M : Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b Φ with hM
  have htr : LinearMap.trace k V Φ = M 0 0 + M 1 1 := by
    rw [LinearMap.trace_eq_matrix_trace k b Φ, Matrix.trace_fin_two]

  have hmat : M * M - t • M + n • (1 : Matrix (Fin 2) (Fin 2) k) = 0 := by
    have := congrArg (LinearMap.toMatrix b b) hΦ
    rw [map_add, map_sub, map_zero, map_smul, map_smul, LinearMap.toMatrix_mul, LinearMap.toMatrix_one] at this
    simpa [hM] using this
  have e : ∀ i j : Fin 2, (M * M - t • M + n • (1 : Matrix (Fin 2) (Fin 2) k)) i j = 0 := fun i j => by
    rw [hmat]; rfl
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_one, mul_zero, add_zero] at e00 e01 e10 e11
  rw [htr]
  linear_combination (-(M 0 0 - M 1 1) + 2 * (M 0 0 + M 1 1 - t)) * e00 + ((M 0 0 - M 1 1) + 2 * (M 0 0 + M 1 1 - t)) * e11
    - 4 * M 0 1 * e10


-- created on 2026-10-05
