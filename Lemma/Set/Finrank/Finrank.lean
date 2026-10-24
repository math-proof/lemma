import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Submodule_finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image.lean)
-/
@[path]
private lemma main
  {S K : Type} [CommRing S] [Field K] [Algebra S K]
    (L₀ L₁ : Submodule S (Fin 2 → S)) (hL : IsCompl L₀ L₁)
    (M₀ M₁ : Submodule K (Fin 2 → K)) (hM : IsCompl M₀ M₁)
    (h₀ : M₀ = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (L₀ : Set (Fin 2 → S))))
    (h₁ : M₁ = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (L₁ : Set (Fin 2 → S)))) :
    -- imply
    Module.finrank K (K ⊗[S] ↥L₀) = Module.finrank K ↥M₀ ∧ Module.finrank K (K ⊗[S] ↥L₁) = Module.finrank K ↥M₁ := by
    -- proof
  classical
  have hfin : ∀ (P Q : Submodule S (Fin 2 → S)), IsCompl P Q → Module.Finite S ↥P := by
    intro P Q h
    apply Module.Finite.of_surjective
      ((LinearMap.fst S ↥P ↥Q).comp (Submodule.prodEquivOfIsCompl P Q h).symm.toLinearMap)
      (Prod.fst_surjective.comp (Submodule.prodEquivOfIsCompl P Q h).symm.surjective)
  let _ := hfin L₀ L₁ hL
  let _ := hfin L₁ L₀ hL.symm
  let _ : Module.Free K (K ⊗[S] ↥L₀) := Module.Free.of_divisionRing K _
  let _ : Module.Free K (K ⊗[S] ↥L₁) := Module.Free.of_divisionRing K _
  let _ : Module.Finite K (K ⊗[S] ↥L₀) := inferInstance
  let _ : Module.Finite K (K ⊗[S] ↥L₁) := inferInstance
  let φ : ∀ P : Submodule S (Fin 2 → S), K ⊗[S] ↥P →ₗ[K] (Fin 2 → K) := fun P =>
    LinearMap.comp (TensorProduct.piScalarRight S K K (Fin 2)).toLinearMap (P.subtype.baseChange K)
  have hle : ∀ (P : Submodule S (Fin 2 → S)) [Module.Finite S ↥P] (M : Submodule K (Fin 2 → K)),
      M = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (P : Set (Fin 2 → S))) →
      Module.finrank K ↥M ≤ Module.finrank K (K ⊗[S] ↥P) := by
    intro P _ M hMP
    have hMle : M ≤ LinearMap.range (φ P) := by
      rw [hMP, Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨(1 : K) ⊗ₜ[S] ⟨v, hv⟩, ?_⟩
      show TensorProduct.piScalarRight S K K (Fin 2) (P.subtype.baseChange K ((1 : K) ⊗ₜ[S] ⟨v, hv⟩)) = _
      rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      funext j
      show v j • (1 : K) = algebraMap S K (v j)
      rw [Algebra.smul_def, mul_one]
    refine (Submodule.finrank_mono hMle).trans (LinearMap.finrank_range_le (φ P))
  have hsumL : Module.finrank K (K ⊗[S] ↥L₀) + Module.finrank K (K ⊗[S] ↥L₁) = 2 := by
    let e : ((K ⊗[S] ↥L₀) × (K ⊗[S] ↥L₁)) ≃ₗ[K] (Fin 2 → K) :=
      LinearEquiv.trans
        (LinearEquiv.trans (TensorProduct.prodRight S K K ↥L₀ ↥L₁).symm
          (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) (Submodule.prodEquivOfIsCompl L₀ L₁ hL)))
        (TensorProduct.piScalarRight S K K (Fin 2))
    rw [← Module.finrank_prod, e.finrank_eq, Module.finrank_fin_fun]
  have hsumM : Module.finrank K ↥M₀ + Module.finrank K ↥M₁ = 2 := by
    rw [← Module.finrank_prod, (Submodule.prodEquivOfIsCompl M₀ M₁ hM).finrank_eq, Module.finrank_fin_fun]
  have h0 := hle L₀ M₀ h₀
  have h1 := hle L₁ M₁ h₁
  omega


-- created on 2026-10-20
