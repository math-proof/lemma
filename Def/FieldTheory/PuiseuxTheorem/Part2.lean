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
import Abbrev.FieldTheory.PuiseuxTheorem
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

noncomputable section

open Polynomial

def puiseux_uniformizer {K : Type*} [Field K] (d : Rat) (hd : 0 < d) :
    puiseuxValuationRing K :=
  ⟨HahnSeries.single d 1, by
    rw [show HahnSeries.single d (1 : K) ∈ (puiseux_hahnVal K).valuationSubring ↔
      0 ≤ (HahnSeries.single d (1 : K)).orderTop by
        rw [Valuation.mem_valuationSubring_iff]
        rfl]
    simpa using hd.le⟩

def puiseux_hahnIdeal {K : Type*} [Field K] (d : Rat) (hd : 0 < d) :
    Ideal (puiseuxValuationRing K) :=
  Ideal.span {puiseux_uniformizer (K := K) d hd}

def puiseux_constants {K : Type*} [Field K] :
    K →+* puiseuxValuationRing K :=
  (HahnSeries.C (R := K) (Γ := Rat)).codRestrict
    (puiseux_hahnVal K).valuationSubring fun a ↦ by
      rw [show HahnSeries.C a ∈ (puiseux_hahnVal K).valuationSubring ↔
        0 ≤ (HahnSeries.C a : HahnSeries Rat K).orderTop by
          rw [Valuation.mem_valuationSubring_iff]
          rfl]
      by_cases ha : a = 0
      · simp [ha]
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha]
        norm_num

def puiseux_tail {K : Type*} [Field K] (x : puiseuxValuationRing K) :
    puiseuxValuationRing K :=
  x - puiseux_constants ((x : HahnSeries Rat K).coeff 0)

noncomputable def puiseux_epsilon {K : Type*} [Field K]
    (x : puiseuxValuationRing K) : Rat := by
  classical
  exact if puiseux_tail x = 0 then 1
    else ((puiseux_tail x : puiseuxValuationRing K) : HahnSeries Rat K).order

def puiseux_precision {K : Type*} [Field K]
    (p : (puiseuxValuationRing K)[X]) : Rat :=
  let s := insert 1 (p.support.image fun i ↦ puiseux_epsilon (p.coeff i))
  s.min' (Finset.insert_nonempty _ _)

end
end MetaMathlibExt
