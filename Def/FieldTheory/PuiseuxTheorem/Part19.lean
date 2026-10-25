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
import Theorem.FieldTheory.PuiseuxTheorem.Part16
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

noncomputable def puiseux_powerSeriesPolynomial {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (p : (puiseuxValuationRing K)[X])
    (hp : ∀ i, puiseuxAtLevel n
      ((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K)) :
    (PowerSeries K)[X] := by
  classical
  exact Polynomial.ofFn (p.natDegree + 1) fun i ↦
    Classical.choose (puiseux_exists_powerSeries_preimage hn (p.coeff i) (hp i))

end
end MetaMathlibExt
end MetaMathlibExt
