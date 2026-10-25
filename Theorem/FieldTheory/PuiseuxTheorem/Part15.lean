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
import Def.FieldTheory.PuiseuxTheorem.Part17
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_powerSeriesLevelHom_apply {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (x : PowerSeries K) :
    puiseux_powerSeriesLevelHom n hn x =
      puiseux_levelHom n hn (x : LaurentSeries K) :=
  rfl

theorem puiseux_powerSeriesLevelHom_atLevel {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (x : PowerSeries K) :
    puiseuxAtLevel n (puiseux_powerSeriesLevelHom n hn x) := by
  rw [puiseux_powerSeriesLevelHom_apply]
  exact puiseux_levelHom_atLevel hn (x : LaurentSeries K)

theorem puiseux_powerSeriesLevelHom_orderTop_nonneg
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (x : PowerSeries K) :
    (0 : WithTop Rat) ≤ (puiseux_powerSeriesLevelHom n hn x).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro r hr
  by_cases hrange : r ∈ Set.range (puiseux_indexEmbedding n hn)
  · obtain ⟨m, rfl⟩ := hrange
    rw [puiseux_powerSeriesLevelHom_apply, puiseux_levelHom_apply,
      HahnSeries.embDomain_coeff, PowerSeries.coeff_coe]
    have hq : (puiseux_indexEmbedding n hn m : Rat) < 0 := by
      exact_mod_cast hr
    rw [puiseux_indexEmbedding_apply] at hq
    have hnq : (0 : Rat) < n := by exact_mod_cast hn
    have hm : m < 0 := by
      rcases div_neg_iff.mp hq with h | h
      · exact (not_lt_of_ge hnq.le h.2).elim
      · exact_mod_cast h.1
    simp [hm]
  · rw [puiseux_powerSeriesLevelHom_apply, puiseux_levelHom_apply,
      HahnSeries.embDomain_of_notMem_range (f := puiseux_indexEmbedding n hn) hrange]

end
end MetaMathlibExt
end MetaMathlibExt
