import Mathlib
import Structure.ModularCurve_X0
import Abbrev.ModularCurve_IgusaScheme
import Instance.AlgebraicCurve_TwoChartIntegralModel
import Structure.AlgebraicCurve_CurveModel
import Instance.ModularCurve_GeometricBaseChange
import Instance.ModularCurve_ArithmeticGalois
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Def.ModularCurve_SupersingularModuli
import Structure.AlgebraicGeometry_TwoAffineOpenCover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

variable (p : ℕ) [Fact p.Prime]


abbrev DRModel : Scheme.{0} :=
  AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

abbrev DRModel.toBase : DRModel p ⟶ Spec (CommRingCat.of ℤ) :=
  AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

abbrev DRModel.pFibre : Scheme.{0} :=
  AlgebraicCurve.TwoChartIntegralModel.fibre ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) (Ideal.span {(p : ℤ)})

variable {p} in


end ModularCurve

end
