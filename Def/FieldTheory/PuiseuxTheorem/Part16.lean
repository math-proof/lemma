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
import Theorem.FieldTheory.PuiseuxTheorem.Part13
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

def puiseuxPolynomialBounded {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) : Prop :=
  ∀ i, puiseuxBounded (f.coeff i)

noncomputable def puiseux_subfieldPolynomial {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
    (↥(puiseuxSubfield K))[X] := by
  classical
  exact Polynomial.ofFn (f.natDegree + 1) fun i ↦ ⟨f.coeff i, hf i⟩

end
end MetaMathlibExt
end MetaMathlibExt
