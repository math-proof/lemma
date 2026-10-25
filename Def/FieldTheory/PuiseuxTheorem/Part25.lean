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
import Theorem.FieldTheory.PuiseuxTheorem.Part22
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

noncomputable def puiseuxLevelField (K : Type*) [Field K] (n : ℕ) (hn : 0 < n) :
    Subfield (HahnSeries Rat K) :=
  (puiseux_levelHom n hn).fieldRange

noncomputable def puiseux_baseToLevel {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    LaurentSeries K →+* ↥(puiseuxLevelField K n hn) :=
  (puiseux_laurentHom (K := K)).codRestrict (puiseuxLevelField K n hn) fun x ↦ by
    rw [puiseuxLevelField, RingHom.mem_fieldRange]
    exact ⟨puiseux_scaleHom n hn x, puiseux_levelHom_scaleHom hn x⟩

@[instance_reducible]
noncomputable def puiseux_levelAlgebra {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
  (puiseux_baseToLevel n hn).toAlgebra

noncomputable def puiseux_levelGenerator {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (r : Fin n) : ↥(puiseuxLevelField K n hn) :=
  ⟨puiseux_levelHom n hn (HahnSeries.single ((r : ℕ) : ℤ) 1),
    RingHom.mem_fieldRange_self _ _⟩

end
end MetaMathlibExt
end MetaMathlibExt
