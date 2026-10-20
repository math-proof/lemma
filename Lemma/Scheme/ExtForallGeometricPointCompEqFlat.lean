import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsDomain R] {K : Type u} [Field K]
private lemma specMap_apply_eq_bot (ι : R →+* K) (hι : Function.Injective ι)
    (s : Spec (CommRingCat.of K)) :
    (Spec.map (CommRingCat.ofHom ι)) s = (⊥ : PrimeSpectrum R) := by
  rw [Spec.map_apply]
  apply PrimeSpectrum.ext
  change Ideal.comap ι s.asIdeal = ⊥
  have hs : s.asIdeal = ⊥ := by
    let _ := s.isPrime
    exact (Ideal.eq_bot_of_prime s.asIdeal)
  rw [hs]
  exact Ideal.comap_bot_of_injective ι hι
private lemma exists_mem_and_apply_eq_bot {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [LocallyOfFinitePresentation f] {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, f x = (⊥ : PrimeSpectrum R) := by
  obtain ⟨u, hu⟩ := hne
  have hopen : IsOpen (f.base '' U) := f.isOpenMap U hU
  have hgen : (⊥ : PrimeSpectrum R) ⤳ f u := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨x, hxU, hx⟩ := hgen.mem_open hopen ⟨u, hu, rfl⟩
  exact ⟨x, hxU, hx⟩
private lemma epi_specMap_of_field {κ : Type u} [Field κ] {L : Type u} [CommRing L] [Nontrivial L]
    (r : κ →+* L) : Epi (Spec.map (CommRingCat.ofHom r)) := by
  let _ : Flat (Spec.map (CommRingCat.ofHom r)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let _ := r.toAlgebra
    show Module.Flat κ L
    infer_instance
  let _ : Surjective (Spec.map (CommRingCat.ofHom r)) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of L)))
    exact ⟨x, Subsingleton.elim _ _⟩
  exact Flat.epi_of_flat_of_surjective _
/--
[AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat.lean)
-/
@[path]
private lemma main
    {R : Type u} [CommRing R] [IsDomain R] {K : Type u} [Field K] [IsAlgClosed K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [LocallyOfFinitePresentation f]
    [IsReduced X] (g : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated g]
    {φ ψ : X ⟶ Y} (hφ : φ ≫ g = f) (hψ : ψ ≫ g = f)
    (h : ∀ x : Spec (CommRingCat.of K) ⟶ X,
      x ≫ f = Spec.map (CommRingCat.ofHom ι) → x ≫ φ = x ≫ ψ) :
    φ = ψ := by
  classical
  set sK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom ι)
    with hsK
  let pr : pullback f sK ⟶ X := pullback.fst f sK
  let fK : pullback f sK ⟶ Spec (CommRingCat.of K) := pullback.snd f sK
  let _ : LocallyOfFiniteType fK := inferInstance
  let _ := LocallyOfFiniteType.jacobsonSpace fK
  let S : Set X := {x | ∃ q : Spec (CommRingCat.of K) ⟶ X, q ≫ f = sK ∧
    q (IsLocalRing.closedPoint K) = x}
  have hS : Dense S := by
    rw [dense_iff_inter_open]
    intro U hU hne
    obtain ⟨x, hxU, hx⟩ := exists_mem_and_apply_eq_bot f hU hne
    have hpt : f x = sK (IsLocalRing.closedPoint K) := by
      rw [hx, hsK, specMap_apply_eq_bot ι hι]
    obtain ⟨z₀, hz₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := sK) x _ hpt
    have hV : IsOpen (pr ⁻¹' U) := hU.preimage pr.continuous
    have hVne : (pr ⁻¹' U).Nonempty := ⟨z₀, show pr z₀ ∈ U by rw [hz₀]; exact hxU⟩
    obtain ⟨z, hzU, hz⟩ := nonempty_inter_closedPoints hVne hV.isLocallyClosed
    refine ⟨pr z, hzU, ?_⟩
    refine ⟨pointOfClosedPoint fK z hz ≫ pr, ?_, ?_⟩
    · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
    · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  refine ext_of_fromSpecResidueField_eq φ ψ g S hS ?_ (hφ.trans hψ.symm)
  rintro x ⟨q, hq, rfl⟩
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X q
  have hqq := h q hq
  rw [← e, Category.assoc, Category.assoc] at hqq
  let _ := epi_specMap_of_field
    (Scheme.descResidueField (Scheme.stalkClosedPointTo q)).hom
  exact (cancel_epi (Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo q)))).mp hqq

-- created on 2026-10-20
