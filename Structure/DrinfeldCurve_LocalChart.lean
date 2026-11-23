module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Theorem.RingHom.FunctionField

set_option autoImplicit false

public noncomputable section

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


end DrinfeldCurve.LocalChart

end
