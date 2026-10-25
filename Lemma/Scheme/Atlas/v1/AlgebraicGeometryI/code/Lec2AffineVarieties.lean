import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties.Part3
open AlgebraicGeometry CategoryTheory TopologicalSpace


/--
[Theorem2_2_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma Theorem2_2_forward
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of k)}
  [hvar : Definition3_AlgebraicVariety k X f]
  [IsAffine X] :
-- imply
  IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom) := by
-- proof
  haveI : AlgebraicGeometry.IsReduced X := hvar.reduced
  haveI : LocallyOfFiniteType f := hvar.locallyOfFiniteType
  exact ⟨inferInstance, inferInstance,
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance⟩

/--
[Theorem2_2_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma Theorem2_2_backward
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
[thm22_affine_variety_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma thm22_affine_variety_characterization
  {k : Type u}
  [Field k] :
-- imply
  (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [Definition3_AlgebraicVariety k X f] [IsAffine X], IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧ (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A], Definition3_AlgebraicVariety k (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
-- proof
  ⟨fun X f _ _ => Theorem2_2_forward k X f, fun A _ _ _ _ => Theorem2_2_backward k A⟩

/--
[thm31_affine_variety_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma thm31_affine_variety_characterization
  {k : Type u}
  [Field k] :
-- imply
  (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [Definition3_AlgebraicVariety k X f] [IsAffine X], IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧ (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A], Definition3_AlgebraicVariety k (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
-- proof
  thm22_affine_variety_characterization k

/--
[Lemma2_ClosedSubspaceAffine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma Lemma2_ClosedSubspaceAffine
  {X Z : Scheme.{u}}
  {i : Z ⟶ X}
  [IsClosedImmersion i]
  [IsAffine X] :
-- imply
  IsAffine Z :=
-- proof
  isAffine_of_isAffineHom i

/--
[Lemma2_GlobalSectionsSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma Lemma2_GlobalSectionsSurjective
  {X Z : Scheme.{u}}
  {i : Z ⟶ X}
  [IsClosedImmersion i]
  [IsAffine X] :
-- imply
  Function.Surjective i.appTop :=
-- proof
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/--
[Lemma2_combined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma Lemma2_combined
  {X Z : Scheme.{u}}
  {i : Z ⟶ X}
  [IsClosedImmersion i]
  [IsAffine X] :
-- imply
  IsAffine Z ∧ Function.Surjective i.appTop :=
-- proof
  ⟨Lemma2_ClosedSubspaceAffine i, Lemma2_GlobalSectionsSurjective i⟩

/--
[Corollary2_ClosedSubspaceOfVariety](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma Corollary2_ClosedSubspaceOfVariety
  {k : Type u}
  [Field k]
  {X Z : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of k)}
  [Definition3_AlgebraicVariety k X f]
  {i : Z ⟶ X}
  [IsClosedImmersion i]
  [AlgebraicGeometry.IsReduced Z] :
-- imply
  Definition3_AlgebraicVariety k Z (i ≫ f) where locallyOfFiniteType := by
-- proof
  haveI : LocallyOfFiniteType f := Definition3_AlgebraicVariety.locallyOfFiniteType
  infer_instance
  quasiCompact := by
    haveI : QuasiCompact f := Definition3_AlgebraicVariety.quasiCompact
    infer_instance
  reduced := inferInstance

/--
[Theorem2_3_HilbertBasis_PolynomialRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean)
-/
@[path]
lemma Theorem2_3_HilbertBasis_PolynomialRing
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  IsNoetherianRing (MvPolynomial (Fin n) k) :=
-- proof
  inferInstance


-- created on 2026-10-23
