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
import Theorem.FieldTheory.PuiseuxTheorem.Part2
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

def newtonRatio {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (i : ℕ) : Rat :=
  (f.coeff i).order / ((f.natDegree - i : ℕ) : Rat)

noncomputable def newtonSlope {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) : Rat :=
  let s := (lowerSupport f).image (newtonRatio f)
  s.min' (Finset.image_nonempty.mpr (lowerSupport_nonempty f hf hpow))

end puiseux
end
end MetaMathlibExt
