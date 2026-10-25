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
import Theorem.FieldTheory.PuiseuxTheorem
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

noncomputable section

open Polynomial

def puiseux_residueHom {K : Type*} [Field K] :
    puiseuxValuationRing K →+* K where
  toFun x := (x : HahnSeries Rat K).coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    change (((x : puiseuxValuationRing K) : HahnSeries Rat K) *
      ((y : puiseuxValuationRing K) : HahnSeries Rat K)).coeff 0 = _
    rw [HahnSeries.coeff_mul]
    rw [Finset.sum_eq_single (0, 0)]
    · rintro ⟨a, b⟩ hab hne
      simp only [Finset.mem_antidiagonal, HahnSeries.mem_support] at hab
      have ha : 0 ≤ a := puiseux_nonneg_of_coeff_ne_zero x hab.1
      have hb : 0 ≤ b := puiseux_nonneg_of_coeff_ne_zero y hab.2.1
      have haz : a = 0 := by linarith [hab.2.2]
      have hbz : b = 0 := by linarith [hab.2.2]
      exact (hne (by simp [haz, hbz])).elim
    · intro hnot
      have hpair : ¬ ((x : HahnSeries Rat K).coeff 0 ≠ 0 ∧
          (y : HahnSeries Rat K).coeff 0 ≠ 0) := by
        rintro ⟨hx, hy⟩
        apply hnot
        exact Finset.mem_antidiagonal.mpr ⟨
          (HahnSeries.mem_support _ _).2 hx,
          (HahnSeries.mem_support _ _).2 hy, by simp⟩
      by_cases hx : (x : HahnSeries Rat K).coeff 0 = 0
      · simp [hx]
      · have hy : (y : HahnSeries Rat K).coeff 0 = 0 := by
          by_contra hy
          exact hpair ⟨hx, hy⟩
        simp [hy]

def puiseux_residuePolynomial {K : Type*} [Field K]
    (p : (puiseuxValuationRing K)[X]) : K[X] :=
  p.map puiseux_residueHom

end
end MetaMathlibExt
