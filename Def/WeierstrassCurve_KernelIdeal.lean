import Mathlib
import Def.WeierstrassCurve_RationalEnd

namespace WeierstrassCurve

universe u v

variable {F : Type u} [Field F] (k : Type v) [Field k] [Algebra F k] [DecidableEq k]

def kernelIdealSet (W₀ W : WeierstrassCurve F)
    (χ : (W₀.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) :
    Set (rationalEndSubring k W₀) :=
  {a | ∃ ρ ∈ rationalHomSet k W W₀,
    (a : AddMonoid.End (W₀.baseChange k).toAffine.Point) = ρ.comp χ}

end WeierstrassCurve
