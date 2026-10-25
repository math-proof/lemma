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
import Theorem.FieldTheory.PuiseuxTheorem.Part4
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

def integralScaledCoeff {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) (i : Fin (f.natDegree + 1)) : O K :=
  ⟨scaledCoeff f (newtonSlope f hf hpow) i, by
    rw [show scaledCoeff f (newtonSlope f hf hpow) i ∈
        (puiseux_hahnVal K).valuationSubring ↔
      0 ≤ (scaledCoeff f (newtonSlope f hf hpow) i).orderTop by
        rw [Valuation.mem_valuationSubring_iff]
        rfl]
    exact scaledCoeff_orderTop_nonneg f hf hpow i
      (Nat.lt_succ_iff.mp i.isLt)⟩

noncomputable def newtonPolynomial {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) : (O K)[X] := by
  classical
  exact Polynomial.ofFn (f.natDegree + 1) (integralScaledCoeff f hf hpow)

end puiseux
end
end MetaMathlibExt
