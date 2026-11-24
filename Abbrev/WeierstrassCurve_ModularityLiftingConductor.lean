module
public import Structure.FLTPrelim_FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Def.FLTPrelim_ModularRep
public import Instance.FLTPrelim_Modularity
public import Def.WeierstrassCurve_Mlc1RowStatement
public import Def.WeierstrassCurve_ModularityProps
public import Def.WeierstrassCurve_Semistability
public import Def.WeierstrassCurve_ThreeFiveSwitchConditioned
set_option autoImplicit false


public section

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
