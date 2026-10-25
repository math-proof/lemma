import Mathlib.AlgebraicGeometry.FunctionField
import Class.AlgebraicCurve_DivisorClassGroup
import Lemma.AlgebraicCurve.CurveModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]

def placesOf (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    Set (Place K C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
    (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring}


end AlgebraicCurve

end
