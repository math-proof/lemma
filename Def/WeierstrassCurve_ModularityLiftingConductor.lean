module
public import Theorem.WeierstrassCurve.FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Def.FLTPrelim_ModularRep
public import Instance.FLTPrelim_Modularity
public import Def.WeierstrassCurve_Mlc1RowStatement
public import Def.WeierstrassCurve_ModularityProps
public import Def.WeierstrassCurve_Semistability
public import Def.WeierstrassCurve_ThreeFiveSwitchConditioned
public import Abbrev.WeierstrassCurve_ModularityLiftingConductor
public import Instance.WeierstrassCurve_ModularityLiftingConductor
set_option autoImplicit false


public section

noncomputable section

namespace WeierstrassCurve


def ModularityLiftingAtConductorOrdinary (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) →
    W.IsResiduallyModular p → W.IsModularModelOfExactConductorLevel

end WeierstrassCurve

end
