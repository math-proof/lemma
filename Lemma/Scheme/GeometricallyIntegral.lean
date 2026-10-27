import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

section

noncomputable instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral := by
  refine ⟨fun {X Y} e hX => ?_⟩
  let _ := hX
  let _ : Nonempty Y := ⟨e.hom.base (Classical.arbitrary X)⟩
  exact isIntegral_of_isOpenImmersion e.inv

private lemma surjective_specMap_of_fields
  {K Ω : Type u} [Field K] [Field Ω] (φ : K →+* Ω) :
  Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

private lemma flat_specMap_of_fields
  {K Ω : Type u} [Field K] [Field Ω] (φ : K →+* Ω) :
  Flat (Spec.map (CommRingCat.ofHom φ)) := by
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
  let _ := φ.toAlgebra
  exact (RingHom.flat_algebraMap_iff (R := K) (S := Ω)).mpr inferInstance

private lemma isReduced_of_flat_of_surjective
  {X Y : Scheme} (π : X ⟶ Y) [Flat π] [Surjective π]
  [IsReduced X] :
  IsReduced Y := by
  have hst : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := π.surjective y
    let ψ := (π.stalkMap x).hom
    let _ := ψ.toAlgebra
    let _ : Module.Flat (Y.presheaf.stalk (π.base x)) (X.presheaf.stalk x) := Flat.stalkMap π x
    let _ : IsLocalHom (algebraMap (Y.presheaf.stalk (π.base x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom ψ)
    let _ : Module.FaithfullyFlat (Y.presheaf.stalk (π.base x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective (algebraMap (Y.presheaf.stalk (π.base x)) (X.presheaf.stalk x))
      (FaithfulSMul.algebraMap_injective _ _)
  exact isReduced_of_isReduced_stalk Y

/--
[AlgebraicGeometry_GeometricallyIntegral_of_isPullback_of_geometricallyIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_GeometricallyIntegral_of_isPullback_of_geometricallyIntegral.lean)
-/
@[path]
private lemma main
  {κ k : Type u} [Field κ] [Field k] [Algebra κ k]
  {C C' : Scheme} (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of k)) (g : C' ⟶ C)
  (h : IsPullback g c' c (Spec.map (CommRingCat.ofHom (algebraMap κ k))))
  [GeometricallyIntegral c'] :
  GeometricallyIntegral c := by
  have hc' : geometrically IsIntegral c' := by
    have := ‹GeometricallyIntegral c'›
    rwa [GeometricallyIntegral.eq_geometrically] at this
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K' _ _
  let _ : Nontrivial (K' ⊗[κ] k) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left (R := κ) K' k (algebraMap κ k).injective
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (K' ⊗[κ] k)
  let Ω : Type u := (K' ⊗[κ] k) ⧸ 𝔪
  let _ : Field Ω := Ideal.Quotient.field 𝔪
  let φK : K' →+* Ω := algebraMap K' Ω
  let φk : k →+* Ω := (Ideal.Quotient.mk 𝔪).comp (Algebra.TensorProduct.includeRight (R := κ) (A := K') (B := k)).toRingHom
  have hφK : φK.comp (algebraMap κ K') = algebraMap κ Ω := (IsScalarTower.algebraMap_eq κ K' Ω).symm
  have hφk : φk.comp (algebraMap κ k) = algebraMap κ Ω := by
    ext a
    change Ideal.Quotient.mk 𝔪 (Algebra.TensorProduct.includeRight (A := K') (algebraMap κ k a)) = algebraMap κ Ω a
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply κ (K' ⊗[κ] k) Ω, Ideal.Quotient.algebraMap_eq]
  let sK : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ K'))
  let sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ k))
  let sΩK : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K') := Spec.map (CommRingCat.ofHom φK)
  let sΩk : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom φk)
  have hcomm : sΩk ≫ sk = sΩK ≫ sK := by
    simp only [sΩk, sk, sΩK, sK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφK, hφk]
  let hint : IsIntegral (pullback c' sΩk) := pullback_of_geometrically hc' Ω sΩk
  have hw : (pullback.fst c' sΩk ≫ g) ≫ c = (pullback.snd c' sΩk ≫ sΩK) ≫ sK := by
    rw [Category.assoc, h.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hcomm]
  let π : pullback c' sΩk ⟶ pullback c sK :=
    pullback.lift (pullback.fst c' sΩk ≫ g) (pullback.snd c' sΩk ≫ sΩK) hw
  have hbig : IsPullback (pullback.fst c' sΩk ≫ g) (pullback.snd c' sΩk) c (sΩK ≫ sK) := by
    rw [← hcomm]
    refine (IsPullback.of_hasPullback c' sΩk).paste_horiz h
  have hsq : IsPullback π (pullback.snd c' sΩk) (pullback.snd c sK) sΩK := by
    refine IsPullback.of_right (h₁₂ := pullback.fst c sK) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c sK)
    unfold π
    rw [pullback.lift_fst]
    refine hbig
  let _ : Surjective π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip (surjective_specMap_of_fields φK)
  let _ : Flat π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip (flat_specMap_of_fields φK)
  let _ : IrreducibleSpace ↥(pullback c sK) := π.surjective.irreducibleSpace π.continuous
  let _ : IsReduced (pullback c sK) := isReduced_of_flat_of_surjective π
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end


-- created on 2026-10-20
