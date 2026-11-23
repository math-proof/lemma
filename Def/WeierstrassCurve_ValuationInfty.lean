module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Norm.Basic

@[expose] public section

open scoped Polynomial.Bivariate WithZero nonZeroDivisors
open Polynomial

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

namespace CoordinateRing

open scoped Classical in

noncomputable def valuationInftyDef (f : W.CoordinateRing) : ℤᵐ⁰ :=
  if f = 0 then 0 else WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ)

noncomputable def valuationInftyInt : Valuation W.CoordinateRing ℤᵐ⁰ where
  toFun := valuationInftyDef W
  map_zero' := if_pos rfl
  map_one' := by
    simp [valuationInftyDef]
  map_mul' f g := by
end CoordinateRing

noncomputable def valuationInfty : Valuation W.FunctionField ℤᵐ⁰ :=
  (CoordinateRing.valuationInftyInt W).extendToLocalization
    (CoordinateRing.nonZeroDivisors_le_supp_primeCompl W) W.FunctionField


end WeierstrassCurve.Affine

end
