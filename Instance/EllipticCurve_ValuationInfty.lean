-- Carved from Lemma/Definitions/Def_EllipticCurve_ValuationInfty.lean: instance decls only.
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Norm.Basic
import Lemma.EllipticCurve.ValuationInfty

open scoped Polynomial.Bivariate WithZero nonZeroDivisors
open Polynomial

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)


instance valuationInfty_isNontrivial : (valuationInfty W).IsNontrivial :=
  ⟨algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)), by
    rw [valuationInfty_X]; exact ⟨WithZero.exp_ne_zero, by decide⟩⟩

instance : IsDiscreteValuationRing (valuationInfty W).valuationSubring := inferInstance

end WeierstrassCurve.Affine
