module
public import Theorem.WeierstrassCurve.FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Theorem.CuspForm.ModularRep
public import Instance.FLTPrelim_Modularity
public import Def.WeierstrassCurve_Mlc1RowStatement
public import Def.WeierstrassCurve_ModularityProps
public import Def.WeierstrassCurve_Semistability
public import Def.WeierstrassCurve_ThreeFiveSwitchConditioned
public import Abbrev.WeierstrassCurve_ModularityLiftingConductor
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_WeierstrassCurve_ModularityLiftingConductor.lean: instance decls only.

noncomputable section


namespace FreyPackage

open WeierstrassCurve WeierstrassCurve.Affine.Point FreyCurve

noncomputable local instance instDecEqQbarLedgerStageTwo :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

end FreyPackage

end
