import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma descendsAlong_isClosedImmersion_surjective_inf_flat_inf_quasicompact :
  DescendsAlong @IsClosedImmersion (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
  ·
    rw [inf_comm]
    apply inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h hfst
  let _ := hfst
  have : IsAffine Y :=
    have : UniversallyInjective g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyInjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : UniversallyClosed g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyClosed) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have hce : Topology.IsClosedEmbedding g.base :=
      .of_continuous_injective_isClosedMap g.continuous g.injective g.isClosedMap
    have : IsAffineHom g := isAffineHom_of_isInducing g hce.isInducing hce.isClosed_range
    isAffine_of_isAffineHom g
  let g₀ : Spec (Y.presheaf.obj (op ⊤)) ⟶ Spec R := Y.isoSpec.inv ≫ g
  have hg : g = Y.isoSpec.hom ≫ g₀ := by simp [g₀]
  have hfst₀ : IsClosedImmersion (pullback.fst (Spec.map φ) g₀) := by
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) = pullback.map _ _ _ _ (𝟙 _) Y.isoSpec.inv (𝟙 _) (by simp) (by simp) ≫ pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    change IsClosedImmersion (pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g))
    rw [heq, cancel_left_of_respectsIso @IsClosedImmersion]
    apply hfst
  rw [hg, cancel_left_of_respectsIso @IsClosedImmersion]
  refine of_pullback_fst_Spec_of_codescendsAlong (P := @IsClosedImmersion) (Q' := RingHom.FaithfullyFlat) (Q := fun f ↦ Function.Surjective f) (P' := @Surjective ⊓ @Flat) RingHom.FaithfullyFlat.codescendsAlong_surjective ?_ ?_ h hfst₀
  ·
    intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]
  ·
    intro _ _ f
    apply HasAffineProperty.SpecMap_iff_of_affineAnd (P := @IsClosedImmersion) (Q := fun f ↦ Function.Surjective f) inferInstance RingHom.surjective_respectsIso f

/--
[AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S]
  (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
  {X Y X' Y' : (Scheme : Type (u + 1))}
  (g : Y ⟶ Spec (CommRingCat.of S))
  (g' : Y' ⟶ Spec (CommRingCat.of S'))
  (cY : Y' ⟶ Y)
  (hY : IsPullback cY g' g (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
  (i : X ⟶ Y)
  (i' : X' ⟶ Y')
  (cX : X' ⟶ X)
  (hX : IsPullback cX i' i cY)
  (h : IsClosedImmersion i') :
  IsClosedImmersion i := by
  have hff : (CommRingCat.ofHom (algebraMap S S')).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  have hfs := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap S S'))).2 hff
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty (Scheme : Type (u + 1))) (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := ⟨⟨hfs.2, hfs.1⟩, inferInstance⟩
  have hcY : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty (Scheme : Type (u + 1))) cY :=
    MorphismProperty.of_isPullback (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hY.flip hq
  let _ : DescendsAlong @IsClosedImmersion (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := descendsAlong_isClosedImmersion_surjective_inf_flat_inf_quasicompact
  apply of_isPullback_of_descendsAlong (P := @IsClosedImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hX.flip hcY h


-- created on 2026-10-20
