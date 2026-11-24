module
public import Mathlib
public import Structure.ModularCurve_X0
public import Abbrev.ModularCurve_IgusaScheme
public import Instance.AlgebraicCurve_TwoChartIntegralModel
public import Structure.AlgebraicCurve_CurveModel
public import Instance.ModularCurve_GeometricBaseChange
public import Instance.ModularCurve_ArithmeticGalois
public import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
public import Def.ModularCurve_SupersingularModuli
public import Structure.AlgebraicGeometry_TwoAffineOpenCover
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing


public section

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
