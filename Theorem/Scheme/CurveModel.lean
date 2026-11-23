module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Class.AlgebraicCurve_DivisorClassGroup
public import Structure.AlgebraicCurve_CurveModel
public import Abbrev.AlgebraicCurve_CurveModel

public noncomputable section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicCurve


namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]


public theorem ffAlgEquiv_apply (M : CurveModel K L) (f : L) : M.ffAlgEquiv f = M.ffEquiv f := rfl


public theorem placeEquiv_apply (M : CurveModel K L) (x : closedPoints M.C) :
    M.placeEquiv x = M.placeOfPoint x := rfl


public theorem pointEquivPlace_apply [IsAlgClosed K] (M : CurveModel K L)
    (p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M.pointEquivPlace p = M.placeOfPoint (pointEquivClosedPoint M.toBase p) := rfl

end CurveModel

end AlgebraicCurve

end
