module

public import Mathlib

@[expose] public section

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

universe u v

variable {F : Type u} {k : Type v} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

def mapPoint : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

@[simps]
def mapPointHom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := mapPoint f
  map_zero' := rfl
  map_add' := mapPoint_add f

universe w in

end WeierstrassCurve

end
