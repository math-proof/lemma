import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Def.WeierstrassCurve_Velu

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


variable (S : Finset (R × R))


structure IsVeluSet : Prop where
  equation : ∀ P ∈ S, W.toAffine.Equation P.1 P.2


end WeierstrassCurve
