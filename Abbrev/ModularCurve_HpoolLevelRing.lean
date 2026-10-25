import Mathlib
import Structure.ModularCurve_X0
import Abbrev.ModularCurve_IgusaScheme
import Instance.AlgebraicCurve_TwoChartIntegralModel

set_option autoImplicit false

noncomputable section

namespace ModularCurve

namespace HpoolLevelRing

variable (p : ℕ) [Fact p.Prime]

abbrev Afin : Type :=
  ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))

set_option synthInstance.maxHeartbeats 200000 in

abbrev AfinAway (f : ℤ) : Type :=
  Localization.Away (algebraMap ℤ (Afin p) f)

set_option synthInstance.maxHeartbeats 200000 in


abbrev levelRing (f : ℤ) (u : Afin p) (g : Polynomial ℤ) : Type :=
  AfinAway p f ⧸ Ideal.span {Polynomial.aeval (algebraMap (Afin p) (AfinAway p f) u) g}

set_option synthInstance.maxHeartbeats 200000 in

end HpoolLevelRing

end ModularCurve

end
