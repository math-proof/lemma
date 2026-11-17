module

public import Def.WeierstrassCurve_OddOrderSummingSet
public import Def.WeierstrassCurve_VeluQuotientOfSums
public import Def.WeierstrassCurve_VeluOrderTwo

@[expose] public section

set_option autoImplicit false

namespace WeierstrassCurve

def fullKernelQuotient {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (N : ℕ) : WeierstrassCurve F :=
  W.veluQuotientOfSums
    (∑ P ∈ W.oddOrderSummingSet Q (N - 1), W.veluGx P.1 P.2)
    (∑ P ∈ W.oddOrderSummingSet Q (N - 1),
      (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2))

end WeierstrassCurve
