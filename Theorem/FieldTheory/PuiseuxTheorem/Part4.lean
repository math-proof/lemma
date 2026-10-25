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
import Def.FieldTheory.PuiseuxTheorem.Part6
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

noncomputable section

open Polynomial

namespace puiseux

theorem scaledCoeff_orderTop_nonneg {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) (i : ℕ) (hi : i ≤ f.natDegree) :
    (0 : WithTop Rat) ≤ (scaledCoeff f (newtonSlope f hf hpow) i).orderTop := by
  by_cases hcoeff : f.coeff i = 0
  · simp [scaledCoeff, hcoeff]
  · rw [scaledCoeff, HahnSeries.orderTop_mul,
      HahnSeries.orderTop_single one_ne_zero,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hcoeff]
    apply WithTop.coe_le_coe.mpr
    by_cases hin : i = f.natDegree
    · subst i
      rw [hf.coeff_natDegree, HahnSeries.order_one]
      simp
    · have hiLower : i ∈ lowerSupport f := by
        apply Finset.mem_erase.mpr
        exact ⟨hin, Polynomial.mem_support_iff.mpr hcoeff⟩
      have hbound := newtonSlope_mul_le_order f hf hpow hiLower
      have hcast : ((f.natDegree - i : ℕ) : Rat) =
          (f.natDegree : Rat) - (i : Rat) := by
        rw [Nat.cast_sub hi]
      rw [hcast] at hbound
      linarith

end puiseux
end
end MetaMathlibExt
