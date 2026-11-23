/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Theorem.Polynomial.HenselFactorization
public import Def.FieldTheory.PuiseuxTheorem.Part3
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

@[expose] public noncomputable section

open Polynomial

namespace puiseux

abbrev O (K : Type*) [Field K] := puiseuxValuationRing K

end puiseux
end
end MetaMathlibExt
