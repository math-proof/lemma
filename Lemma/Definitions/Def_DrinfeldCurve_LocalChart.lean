import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Lemma.Definitions.Def_DrinfeldCurve_FunctionField

set_option autoImplicit false

noncomputable section

open MvPowerSeries IsLocalRing DrinfeldCurve

namespace DrinfeldCurve.LocalChart

variable (q : ℕ) [Fact q.Prime]

def drinfeldForm (O : Type) [CommRing O] : MvPowerSeries (Fin 2) O :=
  X 0 * X 1 ^ q - X 0 ^ q * X 1

structure ChartPresentation (O : Type) [CommRing O] (ϖ : O) where
  f : MvPowerSeries (Fin 2) O
  u : MvPowerSeries (Fin 2) O
  v : MvPowerSeries (Fin 2) O
  isUnit_u : IsUnit u
  isUnit_v : IsUnit v
  f_sub_mem : f - drinfeldForm q O ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ (q + 2)

variable {q}

def ChartPresentation.rel {O : Type} [CommRing O] {ϖ : O} (pr : ChartPresentation q O ϖ) : MvPowerSeries (Fin 2) O :=
  C (ϖ ^ (q + 1)) * pr.v - pr.f * pr.u

abbrev ChartPresentation.Ring {O : Type} [CommRing O] {ϖ : O} (pr : ChartPresentation q O ϖ) : Type :=
  MvPowerSeries (Fin 2) O ⧸ Ideal.span {pr.rel}

end DrinfeldCurve.LocalChart

end
