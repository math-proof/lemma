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
import Def.FieldTheory.PuiseuxTheorem.Part24
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_remainder_term_coeff {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) (m : ℤ) :
    (puiseux_scaleHom n hn (puiseux_residuePart hn (puiseux_remainderFin n hn m) x) *
      HahnSeries.single ((puiseux_remainderFin n hn m : ℕ) : ℤ) 1).coeff m = x.coeff m := by
  rw [HahnSeries.coeff_mul_single, mul_one]
  have harg : m - ((puiseux_remainderFin n hn m : ℕ) : ℤ) =
      (n : ℤ) * (m / (n : ℤ)) := by
    rw [puiseux_remainderFin_val]
    linarith [Int.emod_add_mul_ediv m (n : ℤ)]
  rw [harg, puiseux_scaleHom_apply,
    ← puiseux_scaleIndexEmbedding_apply hn (m / (n : ℤ)), HahnSeries.embDomain_coeff,
    puiseux_coeff_residuePart]
  congr 1
  rw [puiseux_remainderFin_val]
  linarith [Int.emod_add_mul_ediv m (n : ℤ)]

theorem puiseux_other_term_coeff {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) (m : ℤ) (r : Fin n) (hr : r ≠ puiseux_remainderFin n hn m) :
    (puiseux_scaleHom n hn (puiseux_residuePart hn r x) *
      HahnSeries.single ((r : ℕ) : ℤ) 1).coeff m = 0 := by
  rw [HahnSeries.coeff_mul_single, mul_one, puiseux_scaleHom_apply,
    HahnSeries.embDomain_of_notMem_range]
  rintro ⟨q, hq⟩
  apply hr
  apply puiseux_residue_eq_remainder_of_eq hn m q r
  rw [puiseux_scaleIndexEmbedding_apply] at hq
  linarith

theorem puiseux_residue_decomposition {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) :
    (∑ r : Fin n, puiseux_scaleHom n hn (puiseux_residuePart hn r x) *
      HahnSeries.single ((r : ℕ) : ℤ) 1) = x := by
  ext m
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single (puiseux_remainderFin n hn m)]
  · exact puiseux_remainder_term_coeff hn x m
  · intro r _ hr
    exact puiseux_other_term_coeff hn x m r hr
  · simp

end
end MetaMathlibExt
end MetaMathlibExt
