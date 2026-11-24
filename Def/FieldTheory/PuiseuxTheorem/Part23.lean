module
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Theorem.Polynomial.HenselFactorization
public import Theorem.FieldTheory.PuiseuxTheorem.Part20


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

noncomputable def puiseux_scaleHom {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom (puiseux_scaleIndexHom n)
    (puiseux_scaleIndexHom_injective hn) (puiseux_scaleIndexHom_le_iff hn)

end
end MetaMathlibExt
end MetaMathlibExt
