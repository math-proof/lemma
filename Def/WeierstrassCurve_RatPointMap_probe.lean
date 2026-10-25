import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

variable {F k : Type} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}


def ratPointMap : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

end WeierstrassCurve
