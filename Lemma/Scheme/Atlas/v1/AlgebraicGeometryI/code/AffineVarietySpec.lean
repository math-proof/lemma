import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.AffineVarietySpec
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry CategoryTheory


namespace AlgebraicGeometry.Scheme

/--
[IsAffineVariety.globalSections_isReduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietySpec.lean)
-/
@[path]
lemma IsAffineVariety.globalSections_isReduced
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  [X.Over (Spec (.of k))]
  [h : IsAffineVariety k X] :
-- imply
  _root_.IsReduced Γ(X, ⊤) := by
-- proof
  haveI : AlgebraicGeometry.IsReduced X := h.isReduced
  infer_instance

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/--
[IsAffineVariety.appTop_finiteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietySpec.lean)
-/
@[path]
lemma IsAffineVariety.appTop_finiteType
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  [X.Over (Spec (.of k))]
  [h : IsAffineVariety k X] :
-- imply
  RingHom.FiniteType ((X ↘ Spec (.of k)).appTop.hom) := by
-- proof
  haveI : IsAffine X := ⟨h.toSpecΓ_isIso⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := h.locallyOfFiniteType
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/--
[Theorem2_2_affineVariety_iff_spec_IsAffineVariety](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietySpec.lean)
-/
@[path]
lemma Theorem2_2_affineVariety_iff_spec_IsAffineVariety
  {k : Type u}
  [Field k] :
-- imply
  (∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffineVariety k X], IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType ((X ↘ Spec (.of k)).appTop.hom)) ∧ (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [_root_.IsReduced A], IsAffineVariety k (Spec (.of A))) := by
-- proof
  constructor
  · intro X _ h
    exact ⟨h.toSpecΓ_isIso,
      h.globalSections_isReduced,
      h.appTop_finiteType⟩
  · intro A _ _ _ _
    infer_instance
end



-- created on 2026-10-23
