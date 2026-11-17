module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Def.WeierstrassCurve_Velu

public section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


variable (S : Finset (R × R))


structure IsVeluSet : Prop where
  equation : ∀ P ∈ S, W.toAffine.Equation P.1 P.2


end WeierstrassCurve
