import Mathlib
import Class.WeierstrassCurve_GenusOnePic0

set_option autoImplicit false

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F]

variable (W : Affine F) in

class GenusOnePlaceGate.IsCentred [GenusOnePlaceGate W] : Prop where
  XClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ ((GenusOnePlaceGate.pointEquivPlace (W := W)) (Point.some x y h)).toValuationSubring.nonunits
  YClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ ((GenusOnePlaceGate.pointEquivPlace (W := W)) (Point.some x y h)).toValuationSubring.nonunits

end WeierstrassCurve.Affine
