import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

attribute [local instance] RingHomInvPair.of_ringEquiv in
private lemma free_of_isLocalizedModule
  {R : Type*} [CommRing R] (S : Submonoid R)
    {M : Type*} [AddCommGroup M] [Module R M]
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free Rₛ Mₛ := by
  set e := (IsLocalization.algEquiv S (Localization S) Rₛ).toRingEquiv
  have key : Module.Free (Localization S) (LocalizedModule S M) ↔ Module.Free Rₛ Mₛ := by
    apply Module.Free.iff_of_equiv (σ := e)
    refine { __ := IsLocalizedModule.iso S f, map_smul' := ?_ }
    intro r x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S r
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
    simp only [e, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      Module.algebraMap_end_apply,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, IsLocalization.algEquiv_apply,
      IsLocalization.map_id_mk']
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]
  refine key.mp ‹_›
private lemma flat_away_map
  {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] (r : A) [Algebra A A'] [IsLocalization.Away r A'] [Algebra B B']
    [IsLocalization.Away (algebraMap A B r) B']
    (hfree : Module.Free (Localization.Away r) (LocalizedModule (Submonoid.powers r) B)) :
    (IsLocalization.Away.map A' B' (algebraMap A B) r).Flat := by
  let _ : Algebra A' B' := (IsLocalization.Away.map A' B' (algebraMap A B) r).toAlgebra
  let _ : Algebra A B' := ((algebraMap B B').comp (algebraMap A B)).toAlgebra
  let _ : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap B B' (algebraMap A B a) = IsLocalization.Away.map A' B' (algebraMap A B) r (algebraMap A A' a)
    rw [IsLocalization.Away.map, IsLocalization.map_eq])
  have hS : Algebra.algebraMapSubmonoid B (Submonoid.powers r) = Submonoid.powers (algebraMap A B r) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  let _ : IsLocalizedModule (Submonoid.powers r) (IsScalarTower.toAlgHom A B B').toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, hS]
    infer_instance
  let _ : Module.Free (Localization (Submonoid.powers r)) (LocalizedModule (Submonoid.powers r) B) := hfree
  let _ : Module.Free A' B' :=
    free_of_isLocalizedModule (Submonoid.powers r) A' (IsScalarTower.toAlgHom A B B').toLinearMap
  show Module.Flat A' B'
  infer_instance
/--
[AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (π : X ⟶ Y) [IsFinite π] [IsLocallyNoetherian Y]
  (h : ∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (hy : y ∈ U), (let _ := (π.app U).hom.toAlgebra; Module.Free (Localization.AtPrime (hU.primeIdealOf ⟨y, hy⟩).asIdeal) (LocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (X.presheaf.obj (op ((TopologicalSpace.Opens.map π.base).obj U)))))) :
    Flat π ∧ LocallyOfFinitePresentation π := by
  classical
  refine ⟨?_, inferInstance⟩
  have key : ∀ y : Y, ∃ W : Y.Opens, Flat ((morphismRestrict π W)) ∧ y ∈ W := by
    intro y
    obtain ⟨U, hU, hyU, hfree𝔭⟩ := h y
    have hπU : IsAffineOpen (((TopologicalSpace.Opens.map π.base).obj U)) := hU.preimage π
    let _ : Algebra (Y.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map π.base).obj U))) := (π.app U).hom.toAlgebra
    let _ : IsNoetherianRing (Y.presheaf.obj (op U)) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let _ : Module.Finite (Y.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map π.base).obj U))) := IsFinite.finite_app π U hU
    let _ : Module.FinitePresentation (Y.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map π.base).obj U))) := Module.finitePresentation_of_finite _ _
    set 𝔭 := hU.primeIdealOf ⟨y, hyU⟩
    let _ : Module.Free (Localization.AtPrime 𝔭.asIdeal) (LocalizedModule 𝔭.asIdeal.primeCompl (X.presheaf.obj (op ((TopologicalSpace.Opens.map π.base).obj U)))) := hfree𝔭
    obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers 𝔭.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap 𝔭.asIdeal.primeCompl (X.presheaf.obj (op ((TopologicalSpace.Opens.map π.base).obj U)))) (Localization.AtPrime 𝔭.asIdeal)
    refine ⟨Y.basicOpen r, ?_, ?_⟩
    ·
      let _ : IsAffine (Y.basicOpen r) := hU.basicOpen r
      let _ : IsAffine (((TopologicalSpace.Opens.map π.base).obj (Y.basicOpen r))) := (hU.basicOpen r).preimage π
      have hQ : ∀ W : Y.Opens, W = Y.basicOpen r → (π.app W).hom.Flat := by
        rintro W rfl
        let _ := hU.isLocalization_basicOpen r
        let _ := hπU.isLocalization_basicOpen (π.app U r)
        refine (RingHom.Flat.respectsIso.arrow_mk_iso_iff (hU.appBasicOpenIsoAwayMap π hπU r)).mpr ?_
        simp only [CommRingCat.hom_ofHom]
        apply flat_away_map r hfree
      rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), morphismRestrict_appTop]
      refine (RingHom.RespectsIso.cancel_right_isIso RingHom.Flat.respectsIso _ _).mpr ?_
      apply hQ _ (Scheme.Opens.ι_image_top _)
    ·
      let := Y.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
      let _ : IsLocalization.AtPrime (Y.presheaf.stalk y) 𝔭.asIdeal := hU.isLocalization_stalk ⟨y, hyU⟩
      rw [Scheme.mem_basicOpen (hx := hyU)]
      apply (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) 𝔭.asIdeal r).mpr hr
  refine Flat.of_stalkMap _ fun x => ?_
  obtain ⟨W, hW, hxW⟩ := key (π x)
  let _ : Flat (morphismRestrict π W) := hW
  refine (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap π W ⟨x, hxW⟩)).mp (Flat.stalkMap (morphismRestrict π W) ⟨x, hxW⟩)


-- created on 2026-10-20
