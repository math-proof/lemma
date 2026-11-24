module
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Theorem.Polynomial.HenselFactorization
public import Def.FieldTheory.PuiseuxTheorem.Part15


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

theorem puiseux_bounded_natCast {K : Type*} [Field K] (n : ℕ) :
    puiseuxBounded (n : HahnSeries Rat K) := by
  induction n with
  | zero => simpa using (puiseux_bounded_zero (K := K))
  | succ n ih =>
      simpa [Nat.cast_succ] using
        puiseux_bounded_add ih (puiseux_bounded_one (K := K))

end
end MetaMathlibExt
end MetaMathlibExt
