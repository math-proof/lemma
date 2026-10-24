import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open Classical in

def reduceCoord (x : K) : ResidueField R :=
  if h : ∃ r : R, algebraMap R K r = x then residue R h.choose else 0

open Classical in

def reducePoint_alt (W : WeierstrassCurve K) [W.IsMinimal R] :
    W.toAffine.Point → (W.reduction R).toAffine.Point
  | .zero => .zero
  | .some x y _ =>
    if _ : valuation K (maximalIdeal R) x ≤ 1 ∧ valuation K (maximalIdeal R) y ≤ 1 then
      if h' : (W.reduction R).toAffine.Nonsingular (reduceCoord R x) (reduceCoord R y)
        then .some _ _ h'
      else .zero
    else .zero

end WeierstrassCurve

end
