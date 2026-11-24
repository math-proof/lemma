module
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Theorem.Polynomial.HenselFactorization
public import Theorem.FieldTheory.PuiseuxTheorem.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/
namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

def puiseux_indexEmbedding (n : ℕ) (hn : 0 < n) : ℤ ↪o Rat where
  toFun := puiseux_indexHom n
  inj' := puiseux_indexHom_injective hn
  map_rel_iff' := by
    intro a b
    change puiseux_indexHom n a ≤ puiseux_indexHom n b ↔ a ≤ b
    exact puiseux_indexHom_le_iff hn a b

end
end MetaMathlibExt
end MetaMathlibExt
