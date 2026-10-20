import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_finite_pullback_of_isClopen_singleton_of_isAlgebraic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_finite_pullback_of_isClopen_singleton_of_isAlgebraic.lean)
-/
@[path]
private lemma main
    {K : Type u} [Field K] (k : Type u) [Field k] [Algebra K k] [Algebra.IsAlgebraic K k]
    {S : Scheme.{u}} (g : S ⟶ Spec (CommRingCat.of K)) [IrreducibleSpace S] [LocallyOfFiniteType g]
    (c : ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap K k)))))
    (hc : IsClopen ({c} : Set ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap K k)))))) :
    Finite ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap K k)))) := by
  classical
  let _ : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K k))) := by
    rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom]
    exact fun a => Algebra.IsIntegral.isIntegral a
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap K k))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom]
    unfold RingHom.Flat
    infer_instance
  have hclosed : IsClosedMap (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base := (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).isClosedMap
  have hgen : GeneralizingMap (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base := Flat.generalizingMap (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k))))
  have hxcl : IsClosed ({(pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c} : Set ↑S) := by
    have := hclosed _ hc.1
    rwa [Set.image_singleton] at this
  have hxgen : StableUnderGeneralization ({(pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c} : Set ↑S) := by
    have := hgen.stableUnderGeneralization_image hc.2.stableUnderGeneralization
    rwa [Set.image_singleton] at this
  have hηx : genericPoint ↑S = (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c :=
    Set.mem_singleton_iff.mp (hxgen (genericPoint_specializes ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c)) (Set.mem_singleton _))
  have hall : ∀ y : ↑S, y = (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c := by
    intro y
    have h1 : (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c ⤳ y := hηx ▸ genericPoint_specializes y
    have h2 : y ∈ closure ({(pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c} : Set ↑S) := h1.mem_closure
    rwa [hxcl.closure_eq, Set.mem_singleton_iff] at h2
  let _ : Subsingleton ↑S := ⟨fun a b => (hall a).trans (hall b).symm⟩
  let _ : IsClosedImmersion (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hxcl
  let _ : Surjective (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c)) := ⟨by
    intro y
    obtain ⟨z, hz⟩ : (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c ∈ Set.range (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c)).base := by
      rw [Scheme.range_fromSpecResidueField]; rfl
    exact ⟨z, hz.trans (hall y).symm⟩⟩
  let _ : IsFinite (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c) ≫ g) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hG : Finite ↑(pullback (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c) ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap K k)))) := by
    have hfin := (pullback.snd (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c) ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap K k)))).finite_preimage_singleton
      (IsLocalRing.closedPoint k)
    have huniv : (Set.univ : Set ↑(pullback (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c) ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap K k))))).Finite :=
      hfin.subset fun t _ => Subsingleton.elim _ _
    exact Set.finite_univ_iff.mp huniv
  let _ : Finite ↑(pullback (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c)) (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k))))) :=
    Finite.of_equiv _ (Scheme.homeoOfIso (pullbackRightPullbackFstIso g (Spec.map (CommRingCat.ofHom (algebraMap K k))) (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c)))).symm.toEquiv
  exact Finite.of_surjective _ (Surjective.surj (f := pullback.snd (S.fromSpecResidueField ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k)))).base c)) (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K k))))))

-- created on 2026-10-20
