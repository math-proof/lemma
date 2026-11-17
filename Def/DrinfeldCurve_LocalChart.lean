module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Structure.DrinfeldCurve_LocalChart

@[expose] public section

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
