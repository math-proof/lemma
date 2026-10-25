import Structure.FLTPrelim_FreyPackage
import Instance.FLTPrelim_GaloisRep
import Def.FLTPrelim_ModularRep
import Instance.FLTPrelim_Modularity
import Def.WeierstrassCurve_Mlc1RowStatement
import Def.WeierstrassCurve_ModularityProps
import Def.WeierstrassCurve_Semistability
import Def.WeierstrassCurve_ThreeFiveSwitchConditioned

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

abbrev IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  Mlc1IsModularModelOfExactConductorLevel W

namespace IsModularModelOfExactConductorLevel

end IsModularModelOfExactConductorLevel

abbrev ModularityLiftingAtConductor (p : ℕ) : Prop :=
  Mlc1ModularityLiftingAtConductor p


end WeierstrassCurve

namespace FreyPackage

open WeierstrassCurve WeierstrassCurve.Affine.Point FreyCurve

noncomputable local instance instDecEqQbarLedgerStageTwo :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

end FreyPackage

end
