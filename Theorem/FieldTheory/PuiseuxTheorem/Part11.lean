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
import Def.FieldTheory.PuiseuxTheorem.Part13
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_levelHom_pullback {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : HahnSeries Rat K) (hx : puiseuxAtLevel n x) :
    puiseux_levelHom n hn (puiseux_pullback hn x) = x := by
  ext r
  by_cases hr : r ∈ Set.range (puiseux_indexEmbedding n hn)
  · obtain ⟨m, rfl⟩ := hr
    simp [puiseux_levelHom_apply, puiseux_pullback]
  · rw [puiseux_levelHom_apply,
      HahnSeries.embDomain_of_notMem_range (f := puiseux_indexEmbedding n hn) hr]
    symm
    by_contra hcoeff
    obtain ⟨m, hm⟩ := hx r hcoeff
    apply hr
    exact ⟨m, hm.symm⟩

theorem puiseux_atLevel_iff {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : HahnSeries Rat K) :
    puiseuxAtLevel n x ↔ ∃ z : LaurentSeries K, puiseux_levelHom n hn z = x := by
  constructor
  · intro hx
    exact ⟨puiseux_pullback hn x, puiseux_levelHom_pullback hn x hx⟩
  · rintro ⟨z, rfl⟩
    exact puiseux_levelHom_atLevel hn z

end
end MetaMathlibExt
end MetaMathlibExt
