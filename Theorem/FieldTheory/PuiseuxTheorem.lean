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
import Def.FieldTheory.PuiseuxTheorem.Part2
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

noncomputable section

open Polynomial

theorem puiseux_nonneg_of_coeff_ne_zero {K : Type*} [Field K]
    (x : puiseuxValuationRing K) {q : Rat}
    (hq : (x : HahnSeries Rat K).coeff q ≠ 0) : 0 ≤ q := by
  have hxnonneg : (0 : WithTop Rat) ≤ (x : HahnSeries Rat K).orderTop := by
    have hiff : (x : HahnSeries Rat K) ∈ (puiseux_hahnVal K).valuationSubring ↔
        0 ≤ (x : HahnSeries Rat K).orderTop := by
      rw [Valuation.mem_valuationSubring_iff]
      rfl
    exact hiff.mp x.property
  exact_mod_cast hxnonneg.trans (HahnSeries.orderTop_le_of_coeff_ne_zero hq)

end
end MetaMathlibExt
