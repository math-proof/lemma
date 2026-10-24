import Lemma.Definitions.Def_FLTPrelim_FreyPackage
import Lemma.Definitions.Def_FLTPrelim_GaloisRep
import Lemma.Definitions.Def_FLTPrelim_ModularRep
import Lemma.Definitions.Def_FLTPrelim_Modularity
import Lemma.Definitions.Def_WeierstrassCurve_Mlc1RowStatement
import Lemma.Definitions.Def_WeierstrassCurve_ModularityProps
import Lemma.Definitions.Def_WeierstrassCurve_Semistability
import Lemma.Definitions.Def_WeierstrassCurve_ThreeFiveSwitchConditioned

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

abbrev IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  Mlc1IsModularModelOfExactConductorLevel W

namespace IsModularModelOfExactConductorLevel

end IsModularModelOfExactConductorLevel

abbrev ModularityLiftingAtConductor (p : ℕ) : Prop :=
  Mlc1ModularityLiftingAtConductor p

def ModularityLiftingAtConductorOrdinary (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) →
    W.IsResiduallyModular p → W.IsModularModelOfExactConductorLevel

end WeierstrassCurve

namespace FreyPackage

open WeierstrassCurve WeierstrassCurve.Affine.Point FreyCurve

noncomputable local instance instDecEqQbarLedgerStageTwo :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

end FreyPackage

end
