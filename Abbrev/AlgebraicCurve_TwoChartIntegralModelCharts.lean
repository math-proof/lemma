import Mathlib
import Instance.AlgebraicCurve_TwoChartIntegralModel

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux

variable (R₀ : Type u) [CommRing R₀] (F : Type u) [Field F] [Algebra R₀ F] (j : F) [Fact (j ≠ 0)]

set_option quotPrecheck false in
local notation "X₀" => AlgebraicCurve.TwoChartIntegralModel R₀ F j

abbrev ιMid : XMid R₀ F j ⟶ X₀ := fFin R₀ F j ≫ ιFin R₀ F j

abbrev U : (X₀).Opens := (ιFin R₀ F j) ''ᵁ ⊤

abbrev V : (X₀).Opens := (ιInf R₀ F j) ''ᵁ ⊤

end AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux

namespace AlgebraicCurve.TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

abbrev chartFinOpenBC : (baseChange R F j S).Opens := baseChangeι R F j S ⁻¹ᵁ chartFinOpen R F j

abbrev chartInfOpenBC : (baseChange R F j S).Opens := baseChangeι R F j S ⁻¹ᵁ chartInfOpen R F j

end BaseChange

end AlgebraicCurve.TwoChartIntegralModel

end
