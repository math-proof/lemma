import Lemma.ModularCurve.MultCoveringCharts
import Structure.ModularCurve_MultCoveringFamily
import Abbrev.ModularCurve_MultCoveringFamily

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

namespace ModularCurve.MultCovering


theorem coe_frickeInvolutionBar_t {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) :
    ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (zeroSeries Φ l) := by
  rw [Φ.t_eq l, frickeInvolutionBar_def, coe_geomAut_coeffEmb]
  rfl

open Classical in


section PerA
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)


end PerA


end ModularCurve.MultCovering

end
