import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Class.AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicCurve

def baseToFunctionField {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) : K →+* C.functionField :=
  (C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

structure CurveModel (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] where

  C : Scheme.{u}

  toBase : C ⟶ Spec (CommRingCat.of K)

  [isIntegral : IsIntegral C]

  [isProper : IsProper toBase]

  [smooth : SmoothOfRelativeDimension 1 toBase]

  ffEquiv : L ≃+* C.functionField

  ffEquiv_algebraMap : ∀ a : K, ffEquiv (algebraMap K L a) = baseToFunctionField toBase a

  placeOfPoint : closedPoints C → Place K L

  placeOfPoint_bijective : Function.Bijective placeOfPoint

  range_stalk_eq : ∀ x : closedPoints C,
    ((ffEquiv.symm : C.functionField ≃+* L).toRingHom.comp
        (algebraMap (C.presheaf.stalk x.1) C.functionField)).range =
      (placeOfPoint x).toValuationSubring.toSubring

  finset_subset_affineOpen : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

attribute [instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]


end CurveModel

end AlgebraicCurve

end
