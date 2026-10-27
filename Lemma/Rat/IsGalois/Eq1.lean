import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[NumberField_exists_isGalois_compositum](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_exists_isGalois_compositum.lean)
-/
@[path]
private lemma main
  (E F L : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L] [Algebra E F] [Algebra E L] [IsGalois E F] [IsGalois E L] :
  -- imply
  ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra E N) (_ : Algebra F N) (_ : Algebra L N) (_ : IsScalarTower E F N) (_ : IsScalarTower E L N), IsGalois E N ∧ ∀ σ : N ≃ₐ[E] N, (∀ x : F, σ (algebraMap F N x) = algebraMap F N x) → (∀ y : L, σ (algebraMap L N y) = algebraMap L N y) → σ = 1 := by
  -- proof
  classical
  let _ : Module.Finite E F := Module.Finite.of_restrictScalars_finite ℚ E F
  let _ : Module.Finite E L := Module.Finite.of_restrictScalars_finite ℚ E L
  let Ω : Type := AlgebraicClosure E
  let φ : F →ₐ[E] Ω := IsAlgClosed.lift
  let ψ : L →ₐ[E] Ω := IsAlgClosed.lift
  let K₁ : IntermediateField E Ω := φ.fieldRange
  let K₂ : IntermediateField E Ω := ψ.fieldRange
  let S : IntermediateField E Ω := K₁ ⊔ K₂
  let ι₁ : F →ₐ[E] ↥K₁ := φ.codRestrict K₁.toSubalgebra (fun x => AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  let ι₂ : L →ₐ[E] ↥K₂ := ψ.codRestrict K₂.toSubalgebra (fun x => AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  have hι₁ : Function.Bijective ι₁ := by
    refine ⟨fun a b h => φ.injective (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  have hι₂ : Function.Bijective ι₂ := by
    refine ⟨fun a b h => ψ.injective (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  let _ : IsGalois E ↥K₁ := IsGalois.of_algEquiv (AlgEquiv.ofBijective ι₁ hι₁)
  let _ : IsGalois E ↥K₂ := IsGalois.of_algEquiv (AlgEquiv.ofBijective ι₂ hι₂)
  let _ : FiniteDimensional E ↥K₁ := (AlgEquiv.ofBijective ι₁ hι₁).toLinearEquiv.finiteDimensional
  let _ : FiniteDimensional E ↥K₂ := (AlgEquiv.ofBijective ι₂ hι₂).toLinearEquiv.finiteDimensional
  let _ : FiniteDimensional E ↥S := IntermediateField.finiteDimensional_sup K₁ K₂
  let _ : IsGalois E ↥S := inferInstance
  let _ : NumberField ↥S := NumberField.of_module_finite E ↥S
  let jF : F →ₐ[E] ↥S := (IntermediateField.inclusion le_sup_left).comp ι₁
  let jL : L →ₐ[E] ↥S := (IntermediateField.inclusion le_sup_right).comp ι₂
  let algF : Algebra F ↥S := jF.toRingHom.toAlgebra
  let algL : Algebra L ↥S := jL.toRingHom.toAlgebra
  let tF : IsScalarTower E F ↥S := IsScalarTower.of_algebraMap_eq fun x => (jF.commutes x).symm
  let tL : IsScalarTower E L ↥S := IsScalarTower.of_algebraMap_eq fun x => (jL.commutes x).symm
  refine ⟨↥S, inferInstance, inferInstance, inferInstance, algF, algL, tF, tL, inferInstance, ?_⟩
  intro σ hF hL
  have h1 : ∀ (z : Ω) (hz : z ∈ S), σ ⟨z, hz⟩ = ⟨z, hz⟩ →
      z ∈ IntermediateField.lift (IntermediateField.fixedField (Subgroup.zpowers σ)) := by
    intro z hz h
    refine (IntermediateField.mem_lift ⟨z, hz⟩).mpr ((IntermediateField.mem_fixedField_iff _ _).mpr ?_)
    intro f hf
    have hσ : σ ∈ MulAction.stabilizer (↥S ≃ₐ[E] ↥S) (⟨z, hz⟩ : ↥S) := h
    refine Subgroup.zpowers_le.mpr hσ hf
  have key : IntermediateField.lift (IntermediateField.fixedField (Subgroup.zpowers σ)) = S := by
    apply le_antisymm (IntermediateField.lift_le _)
    refine sup_le ?_ ?_
    ·
      intro z hz
      obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hz
      apply h1 _ (le_sup_left (b := K₂) hz) (hF x)
    ·
      intro z hz
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hz
      apply h1 _ (le_sup_right (a := K₁) hz) (hL y)
  have hFix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊤ :=
    IntermediateField.lift_injective S (by rw [key, IntermediateField.lift_top])
  have hbot : Subgroup.zpowers σ = ⊥ := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hFix,
      IntermediateField.fixingSubgroup_top]
  refine Subgroup.zpowers_eq_bot.mp hbot


-- created on 2026-10-20
