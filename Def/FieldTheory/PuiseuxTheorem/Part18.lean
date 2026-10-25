/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Valuation.ValuationSubring
import Lemma.Polynomial.HenselFactorization
import Theorem.FieldTheory.PuiseuxTheorem.Part15
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
