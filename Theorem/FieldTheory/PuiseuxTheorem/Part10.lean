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
import Def.FieldTheory.PuiseuxTheorem.Part12
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_levelHom_atLevel {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) : puiseuxAtLevel n (puiseux_levelHom n hn x) := by
  intro r hr
  have hrange : r ∈ Set.range (puiseux_indexEmbedding n hn) := by
    by_contra h
    rw [puiseux_levelHom_apply hn,
      HahnSeries.embDomain_of_notMem_range (f := puiseux_indexEmbedding n hn) h] at hr
    exact hr rfl
  obtain ⟨m, rfl⟩ := hrange
  exact ⟨m, rfl⟩

end
end MetaMathlibExt
end MetaMathlibExt
