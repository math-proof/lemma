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
import Def.FieldTheory.PuiseuxTheorem.Part16
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_bounded_nextCoeff {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
    puiseuxBounded f.nextCoeff := by
  by_cases hn : f.natDegree = 0
  · simp [Polynomial.nextCoeff, hn, puiseux_bounded_zero]
  · simpa [Polynomial.nextCoeff, hn] using hf (f.natDegree - 1)

theorem puiseux_bounded_center {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
    puiseuxBounded (puiseux.center f) := by
  rw [puiseux.center, div_eq_mul_inv]
  exact puiseux_bounded_mul
    (puiseux_bounded_neg (puiseux_bounded_nextCoeff f hf))
    (puiseux_bounded_inv (puiseux_bounded_natCast f.natDegree))

theorem puiseux_depressed_bounded {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
    puiseuxPolynomialBounded (puiseux.depressed f) := by
  let c : ↥(puiseuxSubfield K) := ⟨puiseux.center f, puiseux_bounded_center f hf⟩
  let q : (↥(puiseuxSubfield K))[X] :=
    (puiseux_subfieldPolynomial f hf).comp (X + C c)
  apply puiseux_polynomialBounded_of_eq_map q
  simp [q, c, puiseux.depressed, Polynomial.map_comp,
    puiseux_map_subfieldPolynomial]

theorem puiseux_newtonPolynomial_bounded {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) (hbounded : puiseuxPolynomialBounded f) :
    ∀ i, puiseuxBounded
      (((puiseux.newtonPolynomial f hf hpow).coeff i :
        puiseuxValuationRing K) : HahnSeries Rat K) := by
  intro i
  by_cases hi : i ≤ f.natDegree
  · rw [puiseux.coe_coeff_newtonPolynomial f hf hpow i hi]
    exact puiseux_bounded_mul
      (puiseux_bounded_single _ 1) (hbounded i)
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt <|
      (puiseux.newtonPolynomial_natDegree f hf hpow).symm ▸ hlt]
    exact puiseux_bounded_zero

end
end MetaMathlibExt
end MetaMathlibExt
