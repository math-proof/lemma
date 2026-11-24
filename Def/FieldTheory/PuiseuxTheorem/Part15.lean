module
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Theorem.Polynomial.HenselFactorization
public import Theorem.FieldTheory.PuiseuxTheorem.Part12


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

def puiseuxSubfield (K : Type*) [Field K] : Subfield (HahnSeries Rat K) where
  carrier := {x | puiseuxBounded x}
  zero_mem' := puiseux_bounded_zero
  one_mem' := puiseux_bounded_one
  add_mem' := fun hx hy ↦ puiseux_bounded_add hx hy
  mul_mem' := fun hx hy ↦ puiseux_bounded_mul hx hy
  neg_mem' := fun hx ↦ puiseux_bounded_neg hx
  inv_mem' := fun _ hx ↦ puiseux_bounded_inv hx

end
end MetaMathlibExt
end MetaMathlibExt
