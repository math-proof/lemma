import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w w' ua un ua' un'

private noncomputable def evalT {R : Type u} [CommRing R] (A : Type w) [CommRing A] [Algebra R A] (M' : Type w') [AddCommGroup M'] [Module R M'] : (M' →ₗ[R] A) ⊗[R] M' →ₗ[R] A :=
  TensorProduct.lift LinearMap.id
@[simp] private lemma evalT_tmul {R : Type u} [CommRing R] (A : Type w) [CommRing A] [Algebra R A] (M' : Type w') [AddCommGroup M'] [Module R M'] (δ : M' →ₗ[R] A) (m : M') : evalT (R := R) A M' (δ ⊗ₜ m) = δ m := by
  simp [evalT]
private lemma evalT_bijective {R : Type u} [CommRing R] (S : Submonoid R) (A : Type w) [CommRing A] [Algebra R A] [IsLocalization S A] (M' : Type w') [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M'] [Module.Invertible A M'] : Function.Bijective (evalT (R := R) A M') := by
  let e₁ := (LinearMap.extendScalarsOfIsLocalizationEquiv S A (M := M') (N := A)).restrictScalars R
  let e₂ := (IsLocalization.moduleTensorEquiv S A (Module.Dual A M') M').restrictScalars R
  let β : (M' →ₗ[R] A) ⊗[R] M' →ₗ[R] A :=
    LinearMap.comp ((contractLeft A M').restrictScalars R) (LinearMap.comp e₂.symm.toLinearMap (TensorProduct.map e₁.toLinearMap LinearMap.id))
  have hβ : β = evalT (R := R) A M' := by
    apply TensorProduct.ext'
    intro δ m
    simp only [β, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, evalT_tmul, LinearMap.restrictScalars_apply]
    have : e₂.symm (e₁ δ ⊗ₜ[R] m) = (e₁ δ) ⊗ₜ[A] m := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [this, contractLeft_apply]
    rfl
  rw [← hβ]
  apply Module.Invertible.bijective.comp (e₂.symm.bijective.comp (TensorProduct.congr e₁ (LinearEquiv.refl R M')).bijective)
private lemma fp_of_localizationSpan {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (s : Set R) (hs : Ideal.span s = ⊤) {Mₚ : ↥s → Type w'} [∀ r : ↥s, AddCommGroup (Mₚ r)] [∀ r : ↥s, Module R (Mₚ r)] {Rₚ : ↥s → Type u} [∀ r : ↥s, CommRing (Rₚ r)] [∀ r : ↥s, Algebra R (Rₚ r)] [∀ r : ↥s, IsLocalization.Away (r.1 : R) (Rₚ r)] [∀ r : ↥s, Module (Rₚ r) (Mₚ r)] [∀ r : ↥s, IsScalarTower R (Rₚ r) (Mₚ r)] (ϕ : ∀ r : ↥s, M →ₗ[R] Mₚ r) [∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r.1 : R)) (ϕ r)] (h : ∀ r : ↥s, Module.FinitePresentation (Rₚ r) (Mₚ r)) : Module.FinitePresentation R M := by
  have : Module.Finite R M := Module.Finite.of_localizationSpan' (Rₚ := Rₚ) s hs ϕ (fun _ => inferInstance)
  obtain ⟨n, f, fsurj⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsurj]
  have H : ∀ g : ↥s, ((LinearMap.ker f).localized' (Rₚ g) (Submonoid.powers (g.1 : R)) (TensorProduct.mk R (Rₚ g) (Fin n → R) 1)).FG := by
    intro g
    rw [LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ g) (Submonoid.powers (g.1 : R)) _ (ϕ g) f]
    apply Module.FinitePresentation.fg_ker
    rw [← LinearMap.range_eq_top] at fsurj ⊢
    simp [← LinearMap.localized'_range_eq_range_localizedMap (Rₚ g) (Submonoid.powers (g.1 : R)), fsurj]
  rw [← Module.Finite.iff_fg]
  apply Module.Finite.of_localizationSpan' s hs (fun g => (LinearMap.ker f).toLocalized' (Rₚ g) (Submonoid.powers (g.1 : R)) (TensorProduct.mk R (Rₚ g) (Fin n → R) 1)) (fun g => Module.Finite.iff_fg.mpr (H g))
private lemma inv_descent_core {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (s : Set R) (hs : Ideal.span s = ⊤) (Rₚ : ↥s → Type u) [∀ r : ↥s, CommRing (Rₚ r)] [∀ r : ↥s, Algebra R (Rₚ r)] [∀ r : ↥s, IsLocalization.Away (r.1 : R) (Rₚ r)] (Mₚ : ↥s → Type w') [∀ r : ↥s, AddCommGroup (Mₚ r)] [∀ r : ↥s, Module R (Mₚ r)] [∀ r : ↥s, Module (Rₚ r) (Mₚ r)] [∀ r : ↥s, IsScalarTower R (Rₚ r) (Mₚ r)] (φ : ∀ r : ↥s, M →ₗ[R] Mₚ r) [∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r.1 : R)) (φ r)] (H : ∀ r : ↥s, Module.Invertible (Rₚ r) (Mₚ r)) : Module.Invertible R M := by
  let _ : ∀ r : ↥s, Module.FinitePresentation (Rₚ r) (Mₚ r) := fun r => Module.finitePresentation_of_projective _ _
  let hfp : Module.FinitePresentation R M := fp_of_localizationSpan s hs (Mₚ := Mₚ) (Rₚ := Rₚ) φ (fun r => inferInstance)
  let dmap : ∀ r : ↥s, Module.Dual R M →ₗ[R] (Mₚ r →ₗ[R] Rₚ r) := fun r => IsLocalizedModule.map (Submonoid.powers (r.1 : R)) (φ r) (Algebra.linearMap R (Rₚ r))
  let hd : ∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r.1 : R)) (dmap r) := fun r => Module.FinitePresentation.isLocalizedModule_map _ _ _
  let T : ∀ r : ↥s, Module.Dual R M ⊗[R] M →ₗ[R] (Mₚ r →ₗ[R] Rₚ r) ⊗[R] Mₚ r := fun r => TensorProduct.map (dmap r) (φ r)
  let _ : ∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r.1 : R)) (T r) := fun r => inferInstance
  refine ⟨bijective_of_isLocalized_span s hs (fun r => (Mₚ r →ₗ[R] Rₚ r) ⊗[R] Mₚ r) T (fun r => Rₚ r) (fun r => Algebra.linearMap R (Rₚ r)) (contractLeft R M) fun r => ?_⟩
  have hmap : IsLocalizedModule.map (Submonoid.powers (r.1 : R)) (T r) (Algebra.linearMap R (Rₚ r)) (contractLeft R M) = evalT (R := R) (Rₚ r) (Mₚ r) := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers (r.1 : R)) (T r) (Algebra.linearMap R (Rₚ r))
    rw [IsLocalizedModule.map_comp]
    apply TensorProduct.ext'
    intro ξ m
    simp only [LinearMap.comp_apply, T, TensorProduct.map_tmul, evalT_tmul, contractLeft_apply, Algebra.linearMap_apply]
    apply (IsLocalizedModule.map_apply (Submonoid.powers (r.1 : R)) (φ r) (Algebra.linearMap R (Rₚ r)) ξ m).symm
  rw [hmap]
  apply evalT_bijective (Submonoid.powers (r.1 : R)) (Rₚ r) (Mₚ r)
private lemma invertible_transfer {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (S : Submonoid R) (A : Type ua) [CommRing A] [Algebra R A] [IsLocalization S A] (N : Type un) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] (φ : M →ₗ[R] N) [IsLocalizedModule S φ] [Module.Invertible A N] (A' : Type ua') [CommRing A'] [Algebra R A'] [IsLocalization S A'] (N' : Type un') [AddCommGroup N'] [Module R N'] [Module A' N'] [IsScalarTower R A' N'] (φ' : M →ₗ[R] N') [IsLocalizedModule S φ'] : Module.Invertible A' N' := by
  let g : A ≃ₗ[R] A' := (IsLocalization.algEquiv S A A').toLinearEquiv
  let e : N ≃ₗ[R] N' := IsLocalizedModule.linearEquiv S φ φ'
  let dA : Module.Dual A N ≃ₗ[R] (N →ₗ[R] A) := ((LinearMap.extendScalarsOfIsLocalizationEquiv S A (M := N) (N := A)).restrictScalars R).symm
  let dA' : (N' →ₗ[R] A') ≃ₗ[R] Module.Dual A' N' := (LinearMap.extendScalarsOfIsLocalizationEquiv S A' (M := N') (N := A')).restrictScalars R
  let ac : (N →ₗ[R] A) ≃ₗ[R] (N' →ₗ[R] A') := LinearEquiv.arrowCongr e g
  let D : Module.Dual A N ≃ₗ[R] Module.Dual A' N' := dA.trans (ac.trans dA')
  let tA : (Module.Dual A N ⊗[A] N) ≃ₗ[R] (Module.Dual A N ⊗[R] N) := (IsLocalization.moduleTensorEquiv S A (Module.Dual A N) N).restrictScalars R
  let tA' : (Module.Dual A' N' ⊗[A'] N') ≃ₗ[R] (Module.Dual A' N' ⊗[R] N') := (IsLocalization.moduleTensorEquiv S A' (Module.Dual A' N') N').restrictScalars R
  let Θ : (Module.Dual A N ⊗[A] N) ≃ₗ[R] (Module.Dual A' N' ⊗[A'] N') := tA.trans ((TensorProduct.congr D e).trans tA'.symm)
  have hD : ∀ (δ : Module.Dual A N) (n : N), (D δ) (e n) = g (δ n) := by
    intro δ n
    show (ac (dA δ)) (e n) = g (δ n)
    rw [LinearEquiv.arrowCongr_apply]
    show g (dA δ (e.symm (e n))) = g (δ n)
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hsq : ∀ z : Module.Dual A N ⊗[A] N, (contractLeft A' N') (Θ z) = g ((contractLeft A N) z) := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro δ n
      have h1 : tA (δ ⊗ₜ[A] n) = δ ⊗ₜ[R] n := rfl
      have h2 : Θ (δ ⊗ₜ[A] n) = tA'.symm (D δ ⊗ₜ[R] e n) := by
        show tA'.symm ((TensorProduct.congr D e) (tA (δ ⊗ₜ[A] n))) = tA'.symm (D δ ⊗ₜ[R] e n)
        rw [h1, TensorProduct.congr_tmul]
      have h3 : tA'.symm (D δ ⊗ₜ[R] e n) = D δ ⊗ₜ[A'] e n := by
        rw [LinearEquiv.symm_apply_eq]
        rfl
      rw [h2, h3, contractLeft_apply, contractLeft_apply, hD]
    ·
      intro x y hx hy
      rw [map_add, map_add, map_add, map_add, hx, hy]
  have hb : Function.Bijective (contractLeft A N) := Module.Invertible.bijective
  have : (contractLeft A' N' : Module.Dual A' N' ⊗[A'] N' → A') = g ∘ (contractLeft A N) ∘ Θ.symm := by
    funext z
    have := hsq (Θ.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    apply this
  refine ⟨?_⟩
  rw [this]
  apply g.bijective.comp (hb.comp Θ.symm.bijective)
private lemma inv_descent {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (s : Set R) (hs : Ideal.span s = ⊤) (Rₚ : ↥s → Type w) [∀ r : ↥s, CommRing (Rₚ r)] [∀ r : ↥s, Algebra R (Rₚ r)] [∀ r : ↥s, IsLocalization.Away (r.1 : R) (Rₚ r)] (Mₚ : ↥s → Type w') [∀ r : ↥s, AddCommGroup (Mₚ r)] [∀ r : ↥s, Module R (Mₚ r)] [∀ r : ↥s, Module (Rₚ r) (Mₚ r)] [∀ r : ↥s, IsScalarTower R (Rₚ r) (Mₚ r)] (φ : ∀ r : ↥s, M →ₗ[R] Mₚ r) [∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r.1 : R)) (φ r)] (H : ∀ r : ↥s, Module.Invertible (Rₚ r) (Mₚ r)) : Module.Invertible R M := by
  let H' : ∀ r : ↥s, Module.Invertible (Localization (Submonoid.powers (r.1 : R))) (LocalizedModule (Submonoid.powers (r.1 : R)) M) := fun r => invertible_transfer (Submonoid.powers (r.1 : R)) (Rₚ r) (Mₚ r) (φ r) _ _ (LocalizedModule.mkLinearMap (Submonoid.powers (r.1 : R)) M)
  apply inv_descent_core s hs (fun r => Localization (Submonoid.powers (r.1 : R))) (fun r => LocalizedModule (Submonoid.powers (r.1 : R)) M) (fun r => LocalizedModule.mkLinearMap (Submonoid.powers (r.1 : R)) M) H'
/--
[Module_Invertible_of_isLocalizedModule_span](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Invertible_of_isLocalizedModule_span.lean)
-/
@[path]
private lemma main
  {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (s : Set R)
  (Rₚ : ↥s → Type w) [∀ r : ↥s, CommRing (Rₚ r)] [∀ r : ↥s, Algebra R (Rₚ r)] [∀ r : ↥s, IsLocalization.Away (r.1 : R) (Rₚ r)]
  (Mₚ : ↥s → Type w') [∀ r : ↥s, AddCommGroup (Mₚ r)] [∀ r : ↥s, Module R (Mₚ r)] [∀ r : ↥s, Module (Rₚ r) (Mₚ r)] [∀ r : ↥s, IsScalarTower R (Rₚ r) (Mₚ r)]
  (φ : ∀ r : ↥s, M →ₗ[R] Mₚ r) [∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r.1 : R)) (φ r)]
  -- given
  (hs : Ideal.span s = ⊤)
  (H : ∀ r : ↥s, Module.Invertible (Rₚ r) (Mₚ r)) :
  -- imply
  Module.Invertible R M :=
  inv_descent s hs Rₚ Mₚ φ H


-- created on 2026-10-20
