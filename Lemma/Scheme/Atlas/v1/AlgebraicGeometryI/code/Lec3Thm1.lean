import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec3Thm1
open AlgebraicGeometry CategoryTheory


/--
[thm3_1_affine_iff_spec_g16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Thm1.lean)
-/
@[path]
lemma thm3_1_affine_iff_spec_g16
  {k : Type v}
  [Field k]
  [IsAlgClosed k] :
-- imply
  (∀ (X : Scheme.{v}) (f : X ⟶ Spec (CommRingCat.of k)) [Definition3_AlgebraicVariety k X f] [IsAffine X], IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧ (∀ (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A], Definition3_AlgebraicVariety k (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
-- proof
  thm31_affine_variety_characterization (k := k)


-- created on 2026-10-23
