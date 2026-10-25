set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_AlgebraicCurve_TwoChartIntegralModelCharts.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace AlgebraicCurve_TwoChartIntegralModelCharts

scoped notation "X₀" => AlgebraicCurve.TwoChartIntegralModel R₀ F j

end AlgebraicCurve_TwoChartIntegralModelCharts
