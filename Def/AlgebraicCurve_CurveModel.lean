module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Class.AlgebraicCurve_DivisorClassGroup
public import Structure.AlgebraicCurve_CurveModel
public import Abbrev.AlgebraicCurve_CurveModel

@[expose] public section

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

def placeEquiv (M : CurveModel K L) : closedPoints M.C ≃ Place K L :=
  Equiv.ofBijective M.placeOfPoint M.placeOfPoint_bijective

def pointEquivPlace [IsAlgClosed K] (M : CurveModel K L) :
    {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} ≃ Place K L :=
  (pointEquivClosedPoint M.toBase).trans M.placeEquiv

end CurveModel

end AlgebraicCurve

end

end
