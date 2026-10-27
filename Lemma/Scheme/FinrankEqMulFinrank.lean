import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma finrank_eq_mul_of_rankAtStalk_eq
  (K B C : Type u) [Field K] [CommRing B] [Algebra K B] [CommRing C] [Algebra B C] [Algebra K C] [IsScalarTower K B C] [Module.Finite K B] [Module.Finite B C] [Module.Flat B C]
  (m : ℕ)
  -- given
  (h : ∀ p : PrimeSpectrum B, Module.rankAtStalk (R := B) C p = m) :
  -- imply
  Module.finrank K C = m * Module.finrank K B := by
  -- proof
  classical
  obtain hB | hB := subsingleton_or_nontrivial B
  ·
    have : Subsingleton C := Module.subsingleton B C
    simp [Module.finrank_zero_of_subsingleton]
  ·
    let _ : IsArtinianRing B := IsArtinianRing.of_finite K B
    have hfree : Module.Free B C := by
      refine Module.free_of_flat_of_finrank_eq (R := B) (M := C) m fun P => ?_
      let _ := P.2
      let _ := Ideal.Quotient.field P.1
      have e := TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ P.1) P.1.ResidueField P.1.ResidueField C
      have h1 : Module.finrank P.1.ResidueField (TensorProduct (B ⧸ P.1) P.1.ResidueField (TensorProduct B (B ⧸ P.1) C)) = Module.finrank (B ⧸ P.1) (TensorProduct B (B ⧸ P.1) C) := Module.finrank_baseChange
      rw [← h1, LinearEquiv.finrank_eq e, Ideal.finrank_fiber_eq_rankAtStalk]
      apply h ⟨P.1, inferInstance⟩
    have hrk : Module.finrank B C = m := by
      obtain ⟨p⟩ : Nonempty (PrimeSpectrum B) := inferInstance
      have := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := B) (M := C)) p
      rw [h p] at this
      apply this.symm
    rw [← Module.finrank_mul_finrank K B C, hrk, mul_comm]

private lemma finrank_comp_SpecMap
  {K : Type u} [Field K]
  {B C : (CommRingCat : Type (u + 1))}
  (ψ : CommRingCat.of K ⟶ B) [IsFinite (Spec.map ψ)] [Flat (Spec.map ψ)]
  (φ : B ⟶ C) [IsFinite (Spec.map φ)] [Flat (Spec.map φ)]
  (m : ℕ)
  -- given
  (hf : ∀ y, (Spec.map φ).finrank y = m)
  (z : Spec (CommRingCat.of K)) :
  -- imply
  (Spec.map φ ≫ Spec.map ψ).finrank z = m * (Spec.map ψ).finrank z := by
  -- proof
  have hψ₁ : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).mp inferInstance
  have hψ₂ : ψ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hφ₁ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  have hφ₂ : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hc₁ : (ψ ≫ φ).hom.Finite := hφ₁.comp hψ₁
  have hc₂ : (ψ ≫ φ).hom.Flat := hψ₂.comp hφ₂
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank hc₁ hc₂, Scheme.Hom.finrank_SpecMap_eq_finrank hψ₁ hψ₂]
  simp_rw [Scheme.Hom.finrank_SpecMap_eq_finrank hφ₁ hφ₂] at hf
  let _ : Algebra K B := ψ.hom.toAlgebra
  let _ : Algebra B C := φ.hom.toAlgebra
  let _ : Algebra K C := (ψ ≫ φ).hom.toAlgebra
  let _ : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq fun x => rfl
  let _ : Module.Finite K B := hψ₁
  let _ : Module.Finite B C := hφ₁
  let _ : Module.Flat B C := hφ₂
  change Module.rankAtStalk (R := K) C z = m * Module.rankAtStalk (R := K) B z
  have hf' : ∀ y : PrimeSpectrum B, Module.rankAtStalk (R := B) C y = m := hf
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq_finrank_of_free]
  apply finrank_eq_mul_of_rankAtStalk_eq K B C m hf'

private lemma finrank_comp_right_of_isIso
  {X Y Y' : (Scheme : Type (u + 1))}
  (f : X ⟶ Y) [IsFinite f] [Flat f]
  (e : Y ⟶ Y') [IsIso e]
  (y : Y) :
  -- imply
  (f ≫ e).finrank (e y) = f.finrank y := by
  -- proof
  have sq : IsPullback (𝟙 X) (f ≫ e) f (inv e) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq]
  congr 1
  simp [← Scheme.Hom.comp_apply]

private lemma finrank_comp_of_field
  {X Y : (Scheme : Type (u + 1))}
  (K : Type u) [Field K]
  (f : X ⟶ Y) [IsFinite f] [Flat f]
  (g : Y ⟶ Spec (CommRingCat.of K)) [IsFinite g] [Flat g]
  (m : ℕ)
  -- given
  (hf : ∀ y, f.finrank y = m)
  (z : Spec (CommRingCat.of K)) :
  -- imply
  (f ≫ g).finrank z = m * g.finrank z := by
  -- proof
  let _ : IsAffine Y := isAffine_of_isAffineHom g
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of K ⟶ Y.presheaf.obj (op ⊤) := Spec.preimage (Y.isoSpec.inv ≫ g)
  let φ : Y.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op ⊤) := Spec.preimage (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  have hg : g = Y.isoSpec.hom ≫ Spec.map ψ := by simp [ψ]
  have hφ : X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom = Spec.map φ := by simp [φ]
  have hfg : f ≫ g = X.isoSpec.hom ≫ (Spec.map φ ≫ Spec.map ψ) := by
    rw [← hφ]
    simp [hg]
  let _ : IsFinite (Spec.map ψ) := by
    have : Spec.map ψ = Y.isoSpec.inv ≫ g := by simp [ψ]
    rw [this]
    infer_instance
  let _ : Flat (Spec.map ψ) := by
    have : Spec.map ψ = Y.isoSpec.inv ≫ g := by simp [ψ]
    rw [this]
    infer_instance
  let _ : IsFinite (Spec.map φ) := by
    rw [← hφ]
    infer_instance
  let _ : Flat (Spec.map φ) := by
    rw [← hφ]
    infer_instance
  have hf' : ∀ y, (Spec.map φ).finrank y = m := by
    intro y
    rw [← hφ, Scheme.Hom.finrank_comp_left_of_isIso]
    obtain ⟨y, rfl⟩ : ∃ y₀ : Y, Y.isoSpec.hom y₀ = y := ⟨Y.isoSpec.inv y, by simp [← Scheme.Hom.comp_apply]⟩
    rw [finrank_comp_right_of_isIso]
    apply hf y
  rw [hfg, hg, Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.hom, Scheme.Hom.finrank_comp_left_of_isIso Y.isoSpec.hom]
  apply finrank_comp_SpecMap ψ φ m hf' z

/--
[AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const.lean)
-/
@[path]
private lemma main
  {X Y Z : (Scheme : Type (u + 1))}
  (f : X ⟶ Y) [IsFinite f] [Flat f]
  (g : Y ⟶ Z) [IsFinite g] [Flat g]
  (m : ℕ)
  -- given
  (hf : ∀ y : Y, f.finrank y = m)
  (z : Z) :
  -- imply
  (f ≫ g).finrank z = m * g.finrank z := by
  -- proof
  let i := Z.fromSpecResidueField z
  obtain ⟨pt⟩ : Nonempty (Spec (Z.residueField z)) := inferInstance
  have hz : i pt = z := Z.fromSpecResidueField_apply z pt
  let f' := pullback.snd f (pullback.fst g i)
  let g' := pullback.snd g i
  have hf' : ∀ y, f'.finrank y = m := fun y => by
    rw [Scheme.Hom.finrank_pullback_snd]
    apply hf
  have key := finrank_comp_of_field (Z.residueField z) f' g' m hf' pt
  have e : f' ≫ g' = (pullbackRightPullbackFstIso g i f).hom ≫ pullback.snd (f ≫ g) i := by
    simp [f', g']
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_pullback_snd, Scheme.Hom.finrank_pullback_snd] at key
  rw [← hz]
  apply key


-- created on 2026-10-20
