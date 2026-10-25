-- Carved from Lemma/Definitions/Def_WeierstrassCurve_ModularityLiftingConductor.lean: instance decls only.
import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Lemma.FLTPrelim.ModularRep
import Instance.FLTPrelim_Modularity
import Def.WeierstrassCurve_Mlc1RowStatement
import Def.WeierstrassCurve_ModularityProps
import Def.WeierstrassCurve_Semistability
import Def.WeierstrassCurve_ThreeFiveSwitchConditioned
import Abbrev.WeierstrassCurve_ModularityLiftingConductor

set_option autoImplicit false

noncomputable section


namespace FreyPackage

open WeierstrassCurve WeierstrassCurve.Affine.Point FreyCurve

noncomputable local instance instDecEqQbarLedgerStageTwo :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

end FreyPackage

end
