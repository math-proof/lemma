import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Class.AlgebraicCurve_DivisorClassGroup
import Structure.AlgebraicCurve_CurveModel
import Abbrev.AlgebraicCurve_CurveModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicCurve


namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

def ffAlgEquiv (M : CurveModel K L) :
    letI := M.functionFieldAlgebra
    L ≃ₐ[K] M.C.functionField :=
  letI := M.functionFieldAlgebra
  AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap

theorem ffAlgEquiv_apply (M : CurveModel K L) (f : L) : M.ffAlgEquiv f = M.ffEquiv f := rfl

def placeEquiv (M : CurveModel K L) : closedPoints M.C ≃ Place K L :=
  Equiv.ofBijective M.placeOfPoint M.placeOfPoint_bijective

theorem placeEquiv_apply (M : CurveModel K L) (x : closedPoints M.C) :
    M.placeEquiv x = M.placeOfPoint x := rfl

def pointEquivPlace [IsAlgClosed K] (M : CurveModel K L) :
    {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} ≃ Place K L :=
  (pointEquivClosedPoint M.toBase).trans M.placeEquiv

theorem pointEquivPlace_apply [IsAlgClosed K] (M : CurveModel K L)
    (p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M.pointEquivPlace p = M.placeOfPoint (pointEquivClosedPoint M.toBase p) := rfl

end CurveModel

end AlgebraicCurve

end
