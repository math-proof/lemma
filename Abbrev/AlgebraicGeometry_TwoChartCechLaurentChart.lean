import Mathlib
import Structure.AlgebraicGeometry_TwoChartCech
import Structure.AlgebraicGeometry_TwoChartCechLaurentChart

set_option autoImplicit false

noncomputable section

universe u v

namespace LaurentSeries

variable (R : Type*) [CommRing R]

end LaurentSeries

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R]


namespace LaurentChart

variable {𝒰 : Cover.{u, v} R} (Λ : 𝒰.LaurentChart)

abbrev expandModule : Module 𝒰.A01 (LaurentSeries R) := Module.compHom (LaurentSeries R) Λ.expand


end LaurentChart

end TwoChartCech.Cover

namespace TwoChartCech.Cover.LaurentChart

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R}


end TwoChartCech.Cover.LaurentChart

namespace TwoChartCech.Cover

end TwoChartCech.Cover

end
