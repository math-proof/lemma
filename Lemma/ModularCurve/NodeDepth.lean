import Lemma.ModularCurve.NodeLocalizedPlaces
import Def.ModularCurve_NodeDepth
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve

section CrossingCoord

variable {ι : Type*} [Fintype ι]


@[simp] theorem crossingCoord_apply (s : ι) (γ : characterLattice ι) :
    crossingCoord s γ = γ.1 s :=
  rfl

end CrossingCoord

end ModularCurve

end
