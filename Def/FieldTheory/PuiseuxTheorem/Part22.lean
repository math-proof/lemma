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
import Theorem.FieldTheory.PuiseuxTheorem.Part19
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

def puiseux_scaleIndexEmbedding (n : ℕ) (hn : 0 < n) : ℤ ↪o ℤ where
  toFun := puiseux_scaleIndexHom n
  inj' := puiseux_scaleIndexHom_injective hn
  map_rel_iff' := by
    intro a b
    change puiseux_scaleIndexHom n a ≤ puiseux_scaleIndexHom n b ↔ a ≤ b
    exact puiseux_scaleIndexHom_le_iff hn a b

end
end MetaMathlibExt
end MetaMathlibExt
