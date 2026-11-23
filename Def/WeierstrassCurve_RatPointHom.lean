module

public import Def.WeierstrassCurve_RatPointMap_probe
public import Theorem.WeierstrassCurve.RatPointHom

@[expose] public section

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

variable {F k : Type} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

@[simps]
def ratPointHom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := ratPointMap f
  map_zero' := rfl
  map_add' := ratPointMap_add f

end WeierstrassCurve
