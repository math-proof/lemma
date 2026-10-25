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
import Def.FieldTheory.PuiseuxTheorem.Part21
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_scaleIndexHom_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (puiseux_scaleIndexHom n) := by
  intro a b hab
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne') hab

theorem puiseux_scaleIndexHom_le_iff {n : ℕ} (hn : 0 < n) (a b : ℤ) :
    puiseux_scaleIndexHom n a ≤ puiseux_scaleIndexHom n b ↔ a ≤ b := by
  change (n : ℤ) * a ≤ (n : ℤ) * b ↔ a ≤ b
  exact Int.mul_le_mul_left (by exact_mod_cast hn)

end
end MetaMathlibExt
end MetaMathlibExt
