import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma injective_of_surjective_of_rankAtStalk_eq
  {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.Flat R A] [Module.Finite R B] [Module.Flat R B]
    (ψ : LinearMap (RingHom.id R) A B) (hψ : Function.Surjective ψ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk A p = Module.rankAtStalk B p) :
    Function.Injective ψ := by
  apply injective_of_localized_maximal
  intro J hJ
  let _ : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl A) :=
    Module.free_of_flat_of_isLocalRing
  let _ : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank (Localization.AtPrime J) (LocalizedModule J.primeCompl A) =
      Module.finrank (Localization.AtPrime J) (LocalizedModule J.primeCompl B) := by
    simpa [Module.rankAtStalk] using h ⟨J, hJ.isPrime⟩
  let e := (LinearEquiv.ofFinrankEq _ _ hrank).symm
  let F := LocalizedModule.map J.primeCompl ψ
  have hF : Function.Surjective F := IsLocalizedModule.map_surjective _ _ _ _ hψ
  have hinj : Function.Injective (e.toLinearMap.comp F) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hF)
  intro x y hxy
  apply hinj
  apply congrArg e hxy
/--
[AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq.lean)
-/
@[path]
private lemma main
  {X Y S : (Scheme : Type (u + 1))} (i : X ⟶ Y) (g : Y ⟶ S) (f : X ⟶ S) (w : i ≫ g = f)
    [IsClosedImmersion i] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : ↥S, f.finrank s = g.finrank s) :
    IsIso i := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  ·
    let 𝒰 := S.affineCover
    rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms Scheme) (𝒰.pullback₁ g)]
    intro j
    let _ : IsFinite f := by
      rw [← w]
      infer_instance
    let V : pullback g (𝒰.f j) ⟶ Y := pullback.fst g (𝒰.f j)
    let i' : pullback i V ⟶ pullback g (𝒰.f j) := pullback.snd i V
    let g' : pullback g (𝒰.f j) ⟶ 𝒰.X j := pullback.snd g (𝒰.f j)
    have sq : IsPullback (i' ≫ g') (pullback.fst i V) (𝒰.f j) (i ≫ g) :=
      (IsPullback.of_hasPullback i V).flip.paste_horiz (IsPullback.of_hasPullback g (𝒰.f j)).flip
    rw [w] at sq
    let _ : Flat (i' ≫ g') := MorphismProperty.of_isPullback sq.flip inferInstance
    let _ : LocallyOfFinitePresentation (i' ≫ g') :=
      MorphismProperty.of_isPullback sq.flip inferInstance
    have h' : ∀ s, (i' ≫ g').finrank s = g'.finrank s := fun s => by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq.flip, Scheme.Hom.finrank_pullback_snd]
      apply h
    simp only [MorphismProperty.isomorphisms.iff]
    apply this i' g' (i' ≫ g') rfl h' ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hS
  wlog hY : ∃ A, Y = Spec A generalizing X Y
  ·
    let _ : IsAffine Y := isAffine_of_isAffineHom g
    rw [← isIso_comp_right_iff i Y.isoSpec.hom]
    refine this (i ≫ Y.isoSpec.hom) (Y.isoSpec.inv ≫ g) f (by simp [w]) (fun s => ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.finrank_comp_left_of_isIso]
    apply h s
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X
  ·
    let _ : IsAffine X := isAffine_of_isAffineHom i
    let _ : IsFinite f := by
      rw [← w]
      infer_instance
    rw [← isIso_comp_left_iff X.isoSpec.inv i]
    refine this (f := X.isoSpec.inv ≫ f) (i := X.isoSpec.inv ≫ i) (by simp [w]) (fun s => ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.finrank_comp_left_of_isIso]
    apply h s
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective i
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨θ, rfl⟩ := Spec.map_surjective f
  have hθ : θ = φ ≫ ψ := Spec.map_injective (by rw [Spec.map_comp, w])
  have hψsurj : Function.Surjective ψ.hom := by
    have H := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ψ)).2
    have e : ψ = (Scheme.ΓSpecIso A).inv ≫ (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso B).hom := by
      simp
    rw [e]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).hom).2.comp
    apply H.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2
  have hθsrc : IsFinite (Spec.map θ) := by
    rw [← w]
    infer_instance
  have hθfin : θ.hom.Finite := (IsFinite.SpecMap_iff θ).mp hθsrc
  have hφfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  simp only [Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
  have h' : ∀ p, θ.hom.finrank p = φ.hom.finrank p := fun p => by
    have := h p
    rwa [Scheme.Hom.finrank_SpecMap_eq_finrank hθfin ‹θ.hom.Flat›,
      Scheme.Hom.finrank_SpecMap_eq_finrank hφfin ‹φ.hom.Flat›] at this
  algebraize [φ.hom, θ.hom]
  have hrk : ∀ p, Module.rankAtStalk (R := R) A p = Module.rankAtStalk (R := R) B p := fun p => by
    have := h' p
    simp only [RingHom.finrank] at this
    apply this.symm
  let ψₗ : LinearMap (RingHom.id R) A B :=
    LinearMap.mk (AddHom.mk ψ.hom (fun a b => map_add _ a b)) (fun r a => by
      simp only [RingHom.id_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, hθ,
        CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply])
  have hinj : Function.Injective ψ.hom :=
    injective_of_surjective_of_rankAtStalk_eq ψₗ hψsurj hrk
  let _ : IsIso ψ := (ConcreteCategory.isIso_iff_bijective ψ).mpr ⟨hinj, hψsurj⟩
  infer_instance


-- created on 2026-10-20
