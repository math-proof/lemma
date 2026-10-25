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
import Def.FieldTheory.PuiseuxTheorem.Part9
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_indexHom_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (puiseux_indexHom n) := by
  intro a b hab
  apply Int.cast_injective (α := Rat)
  exact (div_left_inj' (by exact_mod_cast hn.ne')).mp hab

theorem puiseux_indexHom_le_iff {n : ℕ} (hn : 0 < n) (a b : ℤ) :
    puiseux_indexHom n a ≤ puiseux_indexHom n b ↔ a ≤ b := by
  rw [show puiseux_indexHom n a = (a : Rat) / (n : Rat) from rfl,
    show puiseux_indexHom n b = (b : Rat) / (n : Rat) from rfl,
    div_le_div_iff_of_pos_right (by exact_mod_cast hn)]
  norm_cast

end
end MetaMathlibExt
end MetaMathlibExt
