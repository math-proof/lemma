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
import Def.FieldTheory.PuiseuxTheorem.Part7
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

theorem exists_residuePolynomial_coeff_ne_zero {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) :
    ∃ i < f.natDegree,
      (puiseux_residuePolynomial (newtonPolynomial f hf hpow)).coeff i ≠ 0 := by
  obtain ⟨i, hiLower, hslope⟩ := exists_newtonSlope_eq_ratio f hf hpow
  have hi : i < f.natDegree := lowerSupport_lt_natDegree f hiLower
  have hcoeff : f.coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp (Finset.mem_erase.mp hiLower).2
  have hdenom : (0 : Rat) < (f.natDegree - i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hi
  have hmul : ((f.natDegree - i : ℕ) : Rat) *
      newtonSlope f hf hpow = (f.coeff i).order := by
    rw [hslope, newtonRatio]
    simpa [mul_comm] using
      (div_mul_cancel₀ (f.coeff i).order hdenom.ne')
  have hcast : ((f.natDegree - i : ℕ) : Rat) =
      (f.natDegree : Rat) - (i : Rat) := by
    rw [Nat.cast_sub hi.le]
  rw [hcast] at hmul
  have horder : (scaledCoeff f (newtonSlope f hf hpow) i).orderTop =
      (0 : Rat) := by
    rw [scaledCoeff, HahnSeries.orderTop_mul,
      HahnSeries.orderTop_single one_ne_zero,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hcoeff]
    apply WithTop.coe_eq_coe.mpr
    linarith
  refine ⟨i, hi, ?_⟩
  rw [puiseux_residuePolynomial, Polynomial.coeff_map]
  change (((newtonPolynomial f hf hpow).coeff i : O K) :
    HahnSeries Rat K).coeff 0 ≠ 0
  rw [coe_coeff_newtonPolynomial f hf hpow i hi.le]
  exact HahnSeries.coeff_orderTop_ne horder

theorem residuePolynomial_ne_X_pow {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) :
    puiseux_residuePolynomial (newtonPolynomial f hf hpow) ≠
      X ^ f.natDegree := by
  obtain ⟨i, hi, hcoeff⟩ := exists_residuePolynomial_coeff_ne_zero f hf hpow
  intro heq
  have heqcoeff := congrArg (fun p : K[X] ↦ p.coeff i) heq
  simp only [Polynomial.coeff_X_pow, hi.ne, reduceIte] at heqcoeff
  exact hcoeff heqcoeff

end puiseux
end
end MetaMathlibExt
