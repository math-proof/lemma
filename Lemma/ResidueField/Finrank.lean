import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma finrank_cotangentSpace_eq_of_isLocalization
  {R A S : Type u} [CommRing R] [CommRing A] [CommRing S] [IsLocalRing S]
  [Algebra R A] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
  (M : Submonoid A) [IsLocalization M S] [Nontrivial A]
  (m : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension m R A]
  (hres : Function.Bijective (algebraMap R (IsLocalRing.ResidueField S))) :
  Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.CotangentSpace S) = m := by
  set κ := IsLocalRing.ResidueField S
  let _ : Algebra.IsStandardSmooth R A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth m
  let _ : Algebra.FormallySmooth R A := Algebra.Smooth.formallySmooth
  let _ : Algebra.FormallySmooth A S := Algebra.FormallySmooth.of_isLocalization M
  let _ : Algebra.FormallySmooth R S := Algebra.FormallySmooth.comp R A S
  let _ : Algebra.FormallyEtale A S := Algebra.FormallyEtale.of_isLocalization M
  have hsurj : Function.Surjective (algebraMap S κ) := Ideal.Quotient.mk_surjective
  let _ : Algebra.FormallySmooth R κ :=
    Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R κ) hres)
  have hinj : Function.Injective (KaehlerDifferential.kerCotangentToTensor R S κ) := by
    rw [Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := R) (P := S) (A := κ) hsurj]
    infer_instance
  let _ : Subsingleton (KaehlerDifferential R κ) := KaehlerDifferential.subsingleton_of_surjective R κ hres.2
  have hsurjK : Function.Surjective (KaehlerDifferential.kerCotangentToTensor R S κ) := by
    intro y
    apply Iff.mp (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S κ hsurj y)
    apply Subsingleton.elim
  let e₁ : (RingHom.ker (algebraMap S κ)).Cotangent ≃ₗ[S] TensorProduct S κ (KaehlerDifferential R S) :=
    LinearEquiv.ofBijective _ ⟨hinj, hsurjK⟩
  have hker : IsLocalRing.maximalIdeal S = RingHom.ker (algebraMap S κ) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  let e₀ : IsLocalRing.CotangentSpace S ≃ₗ[S] (RingHom.ker (algebraMap S κ)).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ hker
  let e : IsLocalRing.CotangentSpace S ≃ₗ[κ] TensorProduct S κ (KaehlerDifferential R S) :=
    (e₀.trans e₁).extendScalarsOfSurjective hsurj
  let ebc : TensorProduct A S (KaehlerDifferential R A) ≃ₗ[S] KaehlerDifferential R S :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S
  let _ : Module.Free S (KaehlerDifferential R S) := Module.Free.of_equiv ebc
  have hA : Module.finrank A (KaehlerDifferential R A) = m :=
    Module.finrank_eq_of_rank_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential m)
  have hS : Module.finrank S (KaehlerDifferential R S) = m := by
    rw [← ebc.finrank_eq, Module.finrank_baseChange, hA]
  rw [e.finrank_eq, Module.finrank_baseChange, hS]
private lemma surjective_residueFieldMap_of_section
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) (z : Y ⟶ X)
  (hz : z ≫ f = 𝟙 Y) (y : Y) :
    Function.Surjective (f.residueFieldMap (z.base y)) := by
  have h1 : (z ≫ f).residueFieldMap y = f.residueFieldMap (z.base y) ≫ z.residueFieldMap y :=
    Scheme.residueFieldMap_comp z f y
  have hy : (z ≫ f).base y = (𝟙 Y : Y ⟶ Y).base y := by rw [hz]
  set ε := Y.residueFieldCongr hy with hε
  have h2 : (z ≫ f).residueFieldMap y = ε.hom ≫ (𝟙 Y : Y ⟶ Y).residueFieldMap y :=
    Scheme.Hom.residueFieldMap_congr hz y
  have key : f.residueFieldMap (z.base y) ≫ z.residueFieldMap y = ε.hom ≫ (𝟙 Y : Y ⟶ Y).residueFieldMap y :=
    h1.symm.trans h2
  rw [Scheme.residueFieldMap_id] at key
  intro c
  refine ⟨ε.inv (z.residueFieldMap y c), ?_⟩
  apply (z.residueFieldMap y).hom.injective
  have h3 := congrArg (fun φ => φ.hom (ε.inv (z.residueFieldMap y c))) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
  rw [h3]
  change (ε.inv ≫ ε.hom ≫ 𝟙 _).hom (z.residueFieldMap y c) = _
  rw [Iso.inv_hom_id_assoc]
  rfl
private lemma surjective_evaluation_top_Spec_field (K : Type u) [Field K] (y : Spec (CommRingCat.of K)) :
  Function.Surjective ((Spec (CommRingCat.of K)).evaluation ⊤ y trivial) := by
  have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  let _ : y.asIdeal.IsMaximal := by
    rw [hy]
    apply Ideal.bot_isMaximal
  have hs : Function.Surjective (algebraMap K y.asIdeal.ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have key := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) y
  have h1 : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ y trivial ≫ (Spec (CommRingCat.of K)).residue y) := by
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    apply (Scheme.Spec.residueFieldIso (CommRingCat.of K) y).symm.commRingCatIsoToRingEquiv.surjective.comp hs
  intro c
  obtain ⟨a, ha⟩ := h1 c
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).inv a, ha⟩
private lemma helper_main
  {K : Type u} [Field K] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
  [SmoothOfRelativeDimension n f]
  (z : Spec (CommRingCat.of K) ⟶ X) (hz : z ≫ f = 𝟙 (Spec (CommRingCat.of K))) :
  Module.finrank
    (IsLocalRing.ResidueField (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K))))
    (IsLocalRing.CotangentSpace (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K)))) = n := by
  set x : X := z.base (IsLocalRing.closedPoint K) with hxdef
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  obtain rfl : U = ⊤ := by
    rw [eq_top_iff]
    intro p _
    rw [Subsingleton.elim p (f.base x)]
    apply e hxV
  set R : Type u := ↥((Spec (CommRingCat.of K)).presheaf.obj (op ⊤)) with hR
  set A : Type u := ↥(X.presheaf.obj (op V)) with hA
  set S : Type u := ↥(X.presheaf.stalk x) with hS
  let φ : R →+* A := (f.appLE ⊤ V e).hom
  let algRA : Algebra R A := φ.toAlgebra
  let algAS : Algebra A S := X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
  let algRS : Algebra R S := ((algebraMap A S).comp φ).toAlgebra
  let _ : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsLocalization.AtPrime S (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  have hstdn : Algebra.IsStandardSmoothOfRelativeDimension n R A := hstd
  let _ : Nonempty V := ⟨⟨x, hxV⟩⟩
  let _ : Nontrivial A := inferInstance
  have hcomp : algebraMap R (IsLocalRing.ResidueField S) =
      (f.residueFieldMap x).hom.comp ((Spec (CommRingCat.of K)).evaluation ⊤ (f.base x) trivial).hom := by
    have h1 : algebraMap R (IsLocalRing.ResidueField S) =
        (f.appLE ⊤ V e ≫ X.presheaf.germ V x hxV ≫ X.residue x).hom := by
      rw [IsScalarTower.algebraMap_eq R S (IsLocalRing.ResidueField S), IsLocalRing.ResidueField.algebraMap_eq]
      rfl
    rw [h1, ← CommRingCat.hom_comp, Scheme.evaluation_naturality f x (V := ⊤) trivial]
    congr 1
    simp only [Scheme.Hom.appLE, Category.assoc]
    rw [TopCat.Presheaf.germ_res_assoc]
    rfl
  have hres : Function.Bijective (algebraMap R (IsLocalRing.ResidueField S)) := by
    constructor
    ·
      let ιK := Scheme.ΓSpecIso (CommRingCat.of K)
      have hfac : algebraMap R (IsLocalRing.ResidueField S) =
          ((algebraMap R (IsLocalRing.ResidueField S)).comp ιK.inv.hom).comp ιK.hom.hom := by
        ext r
        simp only [RingHom.coe_comp, Function.comp_apply]
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
        rfl
      rw [hfac]
      apply (RingHom.injective ((algebraMap R (IsLocalRing.ResidueField S)).comp ιK.inv.hom)).comp
        ιK.commRingCatIsoToRingEquiv.injective
    ·
      rw [hcomp]
      apply (surjective_residueFieldMap_of_section f z hz _).comp
        (surjective_evaluation_top_Spec_field K (f.base x))
  refine finrank_cotangentSpace_eq_of_isLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl n hres
/--
[AlgebraicGeometry_finrank_cotangentSpace_eq_of_smoothOfRelativeDimension](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_finrank_cotangentSpace_eq_of_smoothOfRelativeDimension.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
  [SmoothOfRelativeDimension n f]
  (z : Spec (CommRingCat.of K) ⟶ X) (hz : z ≫ f = 𝟙 (Spec (CommRingCat.of K))) :
  Module.finrank
    (IsLocalRing.ResidueField (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K))))
    (IsLocalRing.CotangentSpace (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K)))) = n :=
  helper_main f n z hz


-- created on 2026-10-20
