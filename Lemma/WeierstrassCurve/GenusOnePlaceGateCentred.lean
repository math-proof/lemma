import Mathlib
import Class.WeierstrassCurve_GenusOnePic0
import Class.WeierstrassCurve_GenusOnePlaceGateCentred

set_option autoImplicit false

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F]

namespace GenusOnePlaceGate.IsCentred

variable {W : Affine F} [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

theorem algebraMap_XClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  XClass_mem_nonunits x y h

theorem algebraMap_YClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  YClass_mem_nonunits x y h

end GenusOnePlaceGate.IsCentred

end WeierstrassCurve.Affine
