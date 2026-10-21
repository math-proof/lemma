import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {F : Type*} [Field F]
private noncomputable def normBasis {a b : F} {u v : F}
    (huv : b = u * u - a * (v * v)) :
    QuaternionAlgebra.Basis (R := F) (Matrix (Fin 2) (Fin 2) F) a 0 b where
  i := !![0, a; 1, 0]
  j := !![u, -(a*v); v, -u]
  k := !![a*v, -(a*u); u, -(a*v)]
  i_mul_i := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  j_mul_j := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, huv] <;> ring
  i_mul_j := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  j_mul_i := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
private lemma normBasis_liftHom_apply {a b : F} {u v : F}
    (huv : b = u * u - a * (v * v)) (z : QuaternionAlgebra F a 0 b) :
    (normBasis huv).liftHom z =
      !![z.re + u * z.imJ + a * v * z.imK, a * z.imI - a * v * z.imJ - a * u * z.imK;
         z.imI + v * z.imJ + u * z.imK, z.re - u * z.imJ - a * v * z.imK] := by
  have h : (normBasis huv).liftHom z
      = algebraMap F (Matrix (Fin 2) (Fin 2) F) z.re
        + z.imI • !![(0:F), a; 1, 0] + z.imJ • !![u, -(a*v); v, -u]
        + z.imK • !![a*v, -(a*u); u, -(a*v)] := rfl
  rw [h]
  ext r s; fin_cases r <;> fin_cases s <;>
    simp [Matrix.algebraMap_matrix_apply] <;> ring
/--
[QuaternionAlgebra_nonempty_algEquiv_matrix_of_eq_mul_self_sub](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_eq_mul_self_sub.lean)
-/
@[path]
private lemma main
    {F : Type*} [Field F] [NeZero (2 : F)] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    {u v : F} (huv : b = u * u - a * (v * v)) :
    Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  let φ := (normBasis huv).liftHom
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z0, z1, z2, z3⟩ := z
    rw [normBasis_liftHom_apply] at hz
    have h00 : z0 + u * z2 + a * v * z3 = 0 := by simpa using congrFun (congrFun hz 0) 0
    have h01 : a * z1 - a * v * z2 - a * u * z3 = 0 := by
      simpa using congrFun (congrFun hz 0) 1
    have h10 : z1 + v * z2 + u * z3 = 0 := by simpa using congrFun (congrFun hz 1) 0
    have h11 : z0 - u * z2 - a * v * z3 = 0 := by simpa using congrFun (congrFun hz 1) 1
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have e0 : z0 = 0 := by
      have : (2 : F) * z0 = 0 := by linear_combination h00 + h11
      exact (mul_eq_zero.mp this).resolve_left h2
    have e1 : z1 = 0 := by
      have : (2 : F) * a * z1 = 0 := by linear_combination h01 + a * h10
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero h2 ha)
      · exact h
    have hA : u * z2 + a * v * z3 = 0 := by linear_combination h00 - e0
    have hB : v * z2 + u * z3 = 0 := by linear_combination h10 - e1
    have e2 : z2 = 0 := by
      have : b * z2 = 0 := by linear_combination u * hA - a * v * hB + z2 * huv
      exact (mul_eq_zero.mp this).resolve_left hb
    have e3 : z3 = 0 := by
      have : b * z3 = 0 := by linear_combination (-v) * hA + u * hB + z3 * huv
      exact (mul_eq_zero.mp this).resolve_left hb
    exact QuaternionAlgebra.ext e0 e1 e2 e3
  have hdim : Module.finrank F (QuaternionAlgebra F a 0 b)
      = Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    simp [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix]
  exact ⟨AlgEquiv.ofBijective φ
    (LinearMap.linearEquivOfInjective φ.toLinearMap hinj hdim).bijective⟩

-- created on 2026-10-20
