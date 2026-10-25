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
import Def.FieldTheory.PuiseuxTheorem.Part5
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

theorem newtonSlope_le_ratio {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) {i : ℕ} (hi : i ∈ lowerSupport f) :
    newtonSlope f hf hpow ≤ newtonRatio f i := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem exists_newtonSlope_eq_ratio {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) :
    ∃ i ∈ lowerSupport f, newtonSlope f hf hpow = newtonRatio f i := by
  let s := (lowerSupport f).image (newtonRatio f)
  have hmem := s.min'_mem
    (Finset.image_nonempty.mpr (lowerSupport_nonempty f hf hpow))
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi, by simpa [newtonSlope, s] using heq.symm⟩

theorem lowerSupport_lt_natDegree {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) {i : ℕ} (hi : i ∈ lowerSupport f) :
    i < f.natDegree := by
  have hi' := Finset.mem_erase.mp hi
  exact lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp i hi'.2) hi'.1

theorem newtonSlope_mul_le_order {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) {i : ℕ} (hi : i ∈ lowerSupport f) :
    ((f.natDegree - i : ℕ) : Rat) * newtonSlope f hf hpow ≤
      (f.coeff i).order := by
  have hpos : (0 : Rat) < (f.natDegree - i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lowerSupport_lt_natDegree f hi)
  have hle := newtonSlope_le_ratio f hf hpow hi
  rw [newtonRatio] at hle
  simpa [mul_comm] using (le_div_iff₀ hpos).mp hle

end puiseux
end
end MetaMathlibExt
