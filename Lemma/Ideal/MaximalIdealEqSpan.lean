import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma Scheme.map_comap_stalkSpecializes
  {X : (Scheme : Type (u + 1))} {x y : X} (h : y ⤳ x) (J : Ideal (X.presheaf.stalk y)) :
    (J.comap (X.presheaf.stalkSpecializes h).hom).map (X.presheaf.stalkSpecializes h).hom = J := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  let _ : Algebra (X.presheaf.obj (op U)) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  let _ : Algebra (X.presheaf.obj (op U)) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
  let _ := hU.isLocalization_stalk ⟨x, hxU⟩
  let _ := hU.isLocalization_stalk ⟨y, hyU⟩
  let _ : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let _ : IsScalarTower (X.presheaf.obj (op U)) (X.presheaf.stalk x) (X.presheaf.stalk y) := by
    apply IsScalarTower.of_algebraMap_eq'
    simp_rw [RingHom.algebraMap_toAlgebra]
    change (X.presheaf.germ U y hyU).hom = (X.presheaf.germ U x hxU ≫ X.presheaf.stalkSpecializes h).hom
    rw [X.presheaf.germ_stalkSpecializes]
  have hsp : (⟨y, hyU⟩ : U) ⤳ (⟨x, hxU⟩ : U) := (Topology.IsInducing.subtypeVal.specializes_iff).mp h
  have hle : hU.primeIdealOf ⟨y, hyU⟩ ≤ hU.primeIdealOf ⟨x, hxU⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hsp.map hU.isoSpec.hom.continuous)
  have hle' : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl := by
    intro a ha hay
    apply ha ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hle hay)
  let _ := IsLocalization.isLocalization_of_submonoid_le (X.presheaf.stalk x) (X.presheaf.stalk y) _ _ hle'
  apply IsLocalization.map_under (M := ((hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl.map (algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk x)))) (S := X.presheaf.stalk y) J

private lemma Scheme.stalkSpecializes_genericPoint_closedPoint_injective
  (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] :
    Function.Injective ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes (genericPoint_specializes (IsLocalRing.closedPoint A))).hom :=
  IsFractionRing.injective ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) (Spec (CommRingCat.of A)).functionField

/--
[AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] {X : (Scheme : Type (u + 1))} (c : X ⟶ Spec (CommRingCat.of A))
  (σ : Spec (CommRingCat.of A) ⟶ X) (_ : σ ≫ c = 𝟙 _)
  (t : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A)))
  (ht : RingHom.ker (σ.stalkMap (IsLocalRing.closedPoint A)).hom = Ideal.span {t}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk (σ.base (genericPoint ↥(Spec (CommRingCat.of A))))) = Ideal.span {(X.presheaf.stalkSpecializes (((genericPoint_specializes (IsLocalRing.closedPoint A)).map σ.continuous) : σ.base (genericPoint ↥(Spec (CommRingCat.of A))) ⤳ σ.base (IsLocalRing.closedPoint A))).hom t} := by
  set hs := genericPoint_specializes (α := ↥(Spec (CommRingCat.of A))) (IsLocalRing.closedPoint A)
  set h : σ.base (genericPoint ↥(Spec (CommRingCat.of A))) ⤳ σ.base (IsLocalRing.closedPoint A) := hs.map σ.continuous
  rw [← Scheme.map_comap_stalkSpecializes h (IsLocalRing.maximalIdeal _)]
  suffices hc : (IsLocalRing.maximalIdeal _).comap (X.presheaf.stalkSpecializes h).hom = Ideal.span {t} by
    rw [hc, Ideal.map_span, Set.image_singleton]
    rfl
  rw [← ht]
  ext a
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [← IsLocalRing.maximalIdeal_comap (σ.stalkMap (genericPoint ↥(Spec (CommRingCat.of A)))).hom, Ideal.mem_comap]
  have hnat := Scheme.Hom.stalkSpecializes_stalkMap_apply σ (genericPoint ↥(Spec (CommRingCat.of A))) (IsLocalRing.closedPoint A) hs a
  erw [hnat]
  have hF : IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk (genericPoint ↥(Spec (CommRingCat.of A)))) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField _)
  rw [hF, Ideal.mem_bot]
  apply map_eq_zero_iff _ (Scheme.stalkSpecializes_genericPoint_closedPoint_injective A)


-- created on 2026-10-20
