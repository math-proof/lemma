import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Def.FLTPrelim_ModularRep
import Instance.FLTPrelim_Modularity
import Def.WeierstrassCurve_Mlc1RowStatement
import Def.WeierstrassCurve_ModularityProps
import Def.WeierstrassCurve_Semistability
import Def.WeierstrassCurve_ThreeFiveSwitchConditioned
import Abbrev.WeierstrassCurve_ModularityLiftingConductor
import Instance.WeierstrassCurve_ModularityLiftingConductor

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve


def ModularityLiftingAtConductorOrdinary (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) →
    W.IsResiduallyModular p → W.IsModularModelOfExactConductorLevel

end WeierstrassCurve

end
