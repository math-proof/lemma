import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.SOActionLemma
open SOAction


/--
[isometry_det_sq_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SOActionLemma.lean)
-/
@[path]
private lemma main
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {g : V ≃ₗ[k] V}
-- given
  (hnd : B.Nondegenerate)
  (hiso : ∀ v w, B (g v) (g w) = B v w) :
-- imply
  ((g : V →ₗ[k] V).det) ^ 2 = 1 := by
-- proof
  set b := Module.Free.chooseBasis k V
  set Q := LinearMap.BilinForm.toMatrix b B
  set M := LinearMap.toMatrix b b (g : V →ₗ[k] V)
  have hcomp : B.comp (↑g) (↑g) = B := by
    ext v w; simp [LinearMap.BilinForm.comp_apply, hiso]
  have hmat : Q = M.transpose * Q * M := by
    have := LinearMap.BilinForm.toMatrix_comp b b B (↑g) (↑g)
    rw [hcomp] at this; exact this
  have hQdet : Q.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  rw [show (g : V →ₗ[k] V).det = M.det from by simp [M, LinearMap.det_toMatrix]]
  have h1 : Q.det = (M.transpose * Q * M).det := congr_arg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : (M.det ^ 2 - 1) * Q.det = 0 := by
    have := sub_eq_zero.mpr h1.symm; ring_nf; ring_nf at this; exact this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).elim id (absurd · hQdet))



/--
[isometry_det_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SOActionLemma.lean)
-/
private lemma isometry_det_eq_one_or_neg_one
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {g : V ≃ₗ[k] V}
-- given
  (hnd : B.Nondegenerate)
  (hiso : ∀ v w, B (g v) (g w) = B v w) :
-- imply
  (g : V →ₗ[k] V).det = 1 ∨ (g : V →ₗ[k] V).det = -1 := by
-- proof
  have h := isometry_det_sq_eq_one B hnd g hiso
  have h1 := sub_eq_zero.mpr h
  have h2 : ((g : V →ₗ[k] V).det - 1) * ((g : V →ₗ[k] V).det + 1) = 0 := by
    ring_nf; ring_nf at h1; exact h1
  obtain h3 | h4 := mul_eq_zero.mp h2
  · left; exact sub_eq_zero.mp h3
  · right; exact eq_neg_of_add_eq_zero_left h4



/--
[hyp_swap_det_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SOActionLemma.lean)
-/
private lemma hyp_swap_det_neg_one
  [Field k] :
-- imply
  Matrix.det (!![0, (1 : k); 1, 0]) = -1 := by
-- proof
  rw [Matrix.det_fin_two]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]



/--
[hyp_plane_swap_isometry_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SOActionLemma.lean)
-/
private lemma hyp_plane_swap_isometry_det
  [Field k]
  {e₁ e₂ : Fin 2 → k}
  {b : Module.Basis (Fin 2) k (Fin 2 → k)}
  {g : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k)}
  {a : k}
-- given
  (hb1 : b 0 = e₁)
  (hb2 : b 1 = e₂)
  (ha : a ≠ 0)
  (hge1 : g e₁ = a • e₂)
  (hge2 : g e₂ = a⁻¹ • e₁) :
-- imply
  (g : (Fin 2 → k) →ₗ[k] (Fin 2 → k)).det = -1 := by
-- proof
  rw [show (g : (Fin 2 → k) →ₗ[k] (Fin 2 → k)).det =
    (LinearMap.toMatrix b b (↑g)).det from by simp [LinearMap.det_toMatrix]]
  have hge1' : (↑g : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (b 0) = a • b 1 := by
    simp [hb1, hb2, hge1, LinearEquiv.coe_coe]
  have hge2' : (↑g : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (b 1) = a⁻¹ • b 0 := by
    simp [hb1, hb2, hge2, LinearEquiv.coe_coe]
  have hM : LinearMap.toMatrix b b (↑g) = !![0, a⁻¹; a, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hge1', hge2', Module.Basis.repr_self,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  rw [hM, Matrix.det_fin_two]; simp; exact inv_mul_cancel₀ ha



-- created on 2026-10-23
-- updated on 2026-10-24
