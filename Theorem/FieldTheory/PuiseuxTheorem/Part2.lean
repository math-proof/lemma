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
import Def.FieldTheory.PuiseuxTheorem.Part4
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

theorem lowerSupport_nonempty {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) : (lowerSupport f).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hpow
  ext i
  by_cases hi : i = f.natDegree
  · subst i
    rw [hf.coeff_natDegree]
    simp
  · have hisupp : i ∉ f.support := by
      intro hisupp
      have hiLower : i ∈ lowerSupport f :=
        Finset.mem_erase.mpr ⟨hi, hisupp⟩
      rw [hempty] at hiLower
      simp at hiLower
    rw [Polynomial.notMem_support_iff.mp hisupp]
    simp [Polynomial.coeff_X_pow, hi]

end puiseux
end
end MetaMathlibExt
