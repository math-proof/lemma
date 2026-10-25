import Instance.ModularCurve_MultCoveringCharts
import Structure.ModularCurve_MultCoveringFamily

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

namespace ModularCurve.MultCovering


section PerA
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)


end PerA


abbrev goodFamily {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r) : Fin r → ↥(modularFunctionFieldBar (1 * p)) :=
  Φ.t

end ModularCurve.MultCovering

end
