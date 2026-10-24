import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[BialgHom_exists_coe_eq_of_forall_withConv_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_BialgHom_exists_coe_eq_of_forall_withConv_comp.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {K : Type u} [CommRing K] [Algebra R K]
  {H : Type u} [CommRing H] [Bialgebra R H]
  {H' : Type u} [CommRing H'] [Bialgebra R H']
  {φ : H →ₐ[R] H'}
  -- given
  (hinj : Function.Injective (algebraMap R K))
  (hsep : ∀ x : H' ⊗[R] H', (∀ θ : H' ⊗[R] H' →ₐ[R] K, θ x = 0) → x = 0)
  (hone : (1 : WithConv (H' →ₐ[R] K)).ofConv.comp φ = (1 : WithConv (H →ₐ[R] K)).ofConv)
  (hmul : ∀ χ χ' : WithConv (H' →ₐ[R] K), (χ * χ').ofConv.comp φ = (WithConv.toConv (χ.ofConv.comp φ) * WithConv.toConv (χ'.ofConv.comp φ)).ofConv) :
  -- imply
  ∃ ψ : BialgHom R H H', (ψ : H →ₐ[R] H') = φ := by
  -- proof
  have hcounit : (Bialgebra.counitAlgHom R H').comp φ = Bialgebra.counitAlgHom R H := by
    ext h
    apply hinj
    have := AlgHom.congr_fun hone h
    simpa [AlgHom.convOne_def] using this
  refine ⟨BialgHom.ofAlgHom φ hcounit ?_, rfl⟩
  ext h
  rw [← sub_eq_zero]
  apply hsep
  intro θ
  set χ : H' →ₐ[R] K := θ.comp Algebra.TensorProduct.includeLeft with hχ
  set χ' : H' →ₐ[R] K := θ.comp Algebra.TensorProduct.includeRight with hχ'
  have hθ : θ = Algebra.TensorProduct.lift χ χ' (fun _ _ => Commute.all _ _) := by
    ext a
    all_goals simp [hχ, hχ']
  rw [hθ, map_sub, sub_eq_zero]
  have h1 := AlgHom.congr_fun (hmul (WithConv.toConv χ) (WithConv.toConv χ')) h
  simp only [AlgHom.convMul_def, WithConv.ofConv_toConv, AlgHom.comp_apply] at h1
  have e1 : ∀ (f g : H →ₐ[R] K) (z : H ⊗[R] H), Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z = (Algebra.TensorProduct.lmul' R (S := K)) (Algebra.TensorProduct.map f g z) := by
    intro f g z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro a b
      simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
    ·
      intro a b ha hb
      simp [map_add, ha, hb]
  have e2 : ∀ (f g : H' →ₐ[R] K) (z : H' ⊗[R] H'), Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z = (Algebra.TensorProduct.lmul' R (S := K)) (Algebra.TensorProduct.map f g z) := by
    intro f g z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro a b
      simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
    ·
      intro a b ha hb
      simp [map_add, ha, hb]
  have e3 : ∀ z : H ⊗[R] H, Algebra.TensorProduct.lift χ χ' (fun _ _ => Commute.all _ _) (Algebra.TensorProduct.map φ φ z) = Algebra.TensorProduct.lift (χ.comp φ) (χ'.comp φ) (fun _ _ => Commute.all _ _) z := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro a b
      simp [Algebra.TensorProduct.lift_tmul]
    ·
      intro a b ha hb
      simp [map_add, ha, hb]
  simp only [AlgHom.comp_apply]
  rw [e3, e1, e2]
  apply h1.symm


-- created on 2026-10-20
