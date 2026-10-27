import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.AffineVarietyCharacterization
open AlgebraicGeometry CategoryTheory TopologicalSpace


/--
[affineVariety_isIso_toSpecΓ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean)
-/
@[path]
isomorphism. -/
lemma affineVariety_isIso_toSpecΓ
  (k : Type u) [Field k] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of k))
  [Definition3_AlgebraicVariety k X f] [IsAffine X] :
  IsIso X.toSpecΓ :=
  inferInstance

/--
[affineVariety_globalSections_isReduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean)
-/
@[path]
lemma affineVariety_globalSections_isReduced
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of k)}
  [hvar : Definition3_AlgebraicVariety k X f]
  [IsAffine X] :
-- imply
  _root_.IsReduced Γ(X, ⊤) := by
-- proof
  haveI : AlgebraicGeometry.IsReduced X := hvar.reduced
  infer_instance

/--
[affineVariety_globalSections_finiteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean)
-/
@[path]
lemma affineVariety_globalSections_finiteType
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of k)}
  [hvar : Definition3_AlgebraicVariety k X f]
  [IsAffine X] :
-- imply
  RingHom.FiniteType (f.appTop.hom) := by
-- proof
  haveI : LocallyOfFiniteType f := hvar.locallyOfFiniteType
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance

/--
[affineVariety_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean)
-/
@[path]
lemma affineVariety_forward
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of k)}
  [hvar : Definition3_AlgebraicVariety k X f]
  [IsAffine X] :
-- imply
  IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom) :=
-- proof
  ⟨affineVariety_isIso_toSpecΓ k X f,
    affineVariety_globalSections_isReduced k X f,
    affineVariety_globalSections_finiteType k X f⟩

/--
[affineVariety_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean)
-/
@[path]
lemma affineVariety_backward
  {k : Type u}
  [Field k]
  {A : Type u}
  [CommRing A]
  [Algebra k A]
  [Algebra.FiniteType k A]
  [IsReduced A] :
-- imply
  Definition3_AlgebraicVariety k (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap k A))) where locallyOfFiniteType := by
-- proof
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  rw [show (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap k A))) = (algebraMap k A) from rfl]
  rwa [RingHom.finiteType_algebraMap]
  quasiCompact := inferInstance
  reduced := inferInstance

/--
[affineVariety_iff_spec_fg_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean)
-/
@[path]
lemma affineVariety_iff_spec_fg_reduced
  {k : Type u}
  [Field k] :
-- imply
  (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [Definition3_AlgebraicVariety k X f] [IsAffine X], IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧ (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A], Definition3_AlgebraicVariety k (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
-- proof
  ⟨fun X f _ _ => affineVariety_forward k X f,
    fun A _ _ _ _ => affineVariety_backward k A⟩

/--
[Theorem3_1_affineVariety_iff_fg_reduced_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean)
-/
@[path]
lemma Theorem3_1_affineVariety_iff_fg_reduced_algebra
  {k : Type u}
  [Field k]
  [IsAlgClosed k] :
-- imply
  (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [Definition3_AlgebraicVariety k X f] [IsAffine X], IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧ (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A], Definition3_AlgebraicVariety k (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
-- proof
  affineVariety_iff_spec_fg_reduced k

/--
[affineVariety_isIso_toSpec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean)
-/
@[path]
private lemma affineVariety_isIso_toSpec_eq
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of k)}
  [Definition3_AlgebraicVariety k X f]
  [IsAffine X] :
-- imply
  IsIso X.toSpecΓ := by
-- proof
  apply affineVariety_isIso_toSpec k X f


-- created on 2026-10-23
