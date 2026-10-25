import Instance.ModularCurve_MultCoveringCharts
import Def.ModularCurve_JWidth

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.MultCovering

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]


namespace AnnCtx

variable {Γ : ChartCtx p A} (Δ : AnnCtx Γ)

abbrev annIn (e : Fin (mAnnuli p)) : Annulus A ↥(modularFunctionFieldBar (1 * p)) := Δ.An e

abbrev annOut (e : Fin (mAnnuli p)) : Annulus A ↥(modularFunctionFieldBar (1 * p)) := Δ.An' e


end AnnCtx

end ModularCurve.MultCovering
