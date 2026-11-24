module
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Theorem.Polynomial.HenselFactorization
public import Theorem.FieldTheory.PuiseuxTheorem.Part10


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

noncomputable def puiseux_pullback {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : HahnSeries Rat K) : LaurentSeries K :=
  HahnSeries.mk (fun m : ℤ ↦ x.coeff (puiseux_indexEmbedding n hn m)) <| by
    apply Set.IsWF.isPWO
    have h := Set.WellFoundedOn.mapsTo (puiseux_indexEmbedding n hn) (s := x.support)
      (t := Function.support fun m : ℤ ↦ x.coeff (puiseux_indexEmbedding n hn m))
      (by
        intro m hm
        exact (HahnSeries.mem_support x _).2 hm)
      x.isWF_support
    exact h.mono' fun a _ b _ hab ↦ (puiseux_indexEmbedding n hn).lt_iff_lt.mpr hab

end
end MetaMathlibExt
end MetaMathlibExt
