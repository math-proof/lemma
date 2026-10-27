import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec2AffineVarietySpec
open AlgebraicGeometry CategoryTheory TopologicalSpace


/--
[Theorem2_2_isIso_toSpecΓ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarietySpec.lean)
-/
@[path]
map `X → Spec Γ(X, ⊤)` is an isomorphism. -/
lemma Theorem2_2_isIso_toSpecΓ
  (k : Type u) [Field k] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of k))
  [Definition3_AlgebraicVariety k X f] [IsAffine X] :
  IsIso X.toSpecΓ :=
  inferInstance

/--
[Theorem2_2_globalSections_isReduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarietySpec.lean)
-/
@[path]
lemma Theorem2_2_globalSections_isReduced
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
[Theorem2_2_globalSections_finiteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarietySpec.lean)
-/
@[path]
lemma Theorem2_2_globalSections_finiteType
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
[Theorem2_2_affineVariety_iff_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarietySpec.lean)
-/
@[path]
lemma Theorem2_2_affineVariety_iff_spec
  {k : Type u}
  [Field k] :
-- imply
  (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [Definition3_AlgebraicVariety k X f] [IsAffine X], IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧ (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A], Definition3_AlgebraicVariety k (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
-- proof
  ⟨fun X f _ _ => Theorem2_2_forward k X f,
    fun A _ _ _ _ => Theorem2_2_backward k A⟩

/--
[Theorem2_2_isIso_toSpec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarietySpec.lean)
-/
@[path]
private lemma Theorem2_2_isIso_toSpec_eq
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of k)}
  [Definition3_AlgebraicVariety k X f]
  [IsAffine X] :
-- imply
  IsIso X.toSpecΓ := by
-- proof
  apply Theorem2_2_isIso_toSpec k X f


-- created on 2026-10-23
