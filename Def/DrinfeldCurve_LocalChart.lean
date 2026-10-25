import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Lemma.DrinfeldCurve.FunctionField
import Structure.DrinfeldCurve_LocalChart

set_option autoImplicit false

noncomputable section

open MvPowerSeries IsLocalRing DrinfeldCurve

namespace DrinfeldCurve.LocalChart

variable (q : ℕ) [Fact q.Prime]


variable {q}

def ChartPresentation.rel {O : Type} [CommRing O] {ϖ : O} (pr : ChartPresentation q O ϖ) : MvPowerSeries (Fin 2) O :=
  C (ϖ ^ (q + 1)) * pr.v - pr.f * pr.u

abbrev ChartPresentation.Ring {O : Type} [CommRing O] {ϖ : O} (pr : ChartPresentation q O ϖ) : Type :=
  MvPowerSeries (Fin 2) O ⧸ Ideal.span {pr.rel}

end DrinfeldCurve.LocalChart

end
