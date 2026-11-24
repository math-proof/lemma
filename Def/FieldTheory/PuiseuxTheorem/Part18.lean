module
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Theorem.Polynomial.HenselFactorization
public import Theorem.FieldTheory.PuiseuxTheorem.Part15


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/
namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

noncomputable def puiseux_powerSeriesToValuationRing
    {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    PowerSeries K →+* puiseuxValuationRing K :=
  (puiseux_powerSeriesLevelHom n hn).codRestrict
    (puiseux_hahnVal K).valuationSubring fun x ↦ by
      rw [show puiseux_powerSeriesLevelHom n hn x ∈
          (puiseux_hahnVal K).valuationSubring ↔
        0 ≤ (puiseux_powerSeriesLevelHom n hn x).orderTop by
          rw [Valuation.mem_valuationSubring_iff]
          rfl]
      exact puiseux_powerSeriesLevelHom_orderTop_nonneg hn x

end
end MetaMathlibExt
end MetaMathlibExt
