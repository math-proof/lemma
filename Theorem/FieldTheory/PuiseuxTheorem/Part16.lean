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
import Def.FieldTheory.PuiseuxTheorem.Part18
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_residue_powerSeriesToValuationRing
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (x : PowerSeries K) :
    puiseux_residueHom (puiseux_powerSeriesToValuationRing n hn x) =
      PowerSeries.constantCoeff x := by
  change (puiseux_powerSeriesLevelHom n hn x).coeff 0 =
    PowerSeries.constantCoeff x
  rw [puiseux_powerSeriesLevelHom_apply, puiseux_levelHom_apply]
  rw [← show puiseux_indexEmbedding n hn (0 : ℤ) = 0 by
    simp [puiseux_indexEmbedding_apply]]
  rw [HahnSeries.embDomain_coeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact HahnSeries.ofPowerSeries_apply_coeff x 0

theorem puiseux_exists_powerSeries_preimage {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (x : puiseuxValuationRing K)
    (hx : puiseuxAtLevel n (x : HahnSeries Rat K)) :
    ∃ z : PowerSeries K, puiseux_powerSeriesToValuationRing n hn z = x := by
  let l : LaurentSeries K := puiseux_pullback hn (x : HahnSeries Rat K)
  let z : PowerSeries K := PowerSeries.mk fun k ↦ l.coeff (k : ℤ)
  have hz : (z : LaurentSeries K) = l := by
    ext m
    rw [PowerSeries.coeff_coe]
    by_cases hm : m < 0
    · simp only [hm, reduceIte]
      symm
      by_contra hlm
      have hxcoeff : (x : HahnSeries Rat K).coeff
          (puiseux_indexEmbedding n hn m) ≠ 0 := by
        simpa [l, puiseux_pullback] using hlm
      have hnonneg := puiseux_nonneg_of_coeff_ne_zero x hxcoeff
      have hmrat : (m : Rat) < 0 := by exact_mod_cast hm
      have hnrat : (0 : Rat) < n := by exact_mod_cast hn
      have hneg : puiseux_indexEmbedding n hn m < 0 := by
        rw [puiseux_indexEmbedding_apply]
        exact div_neg_of_neg_of_pos hmrat hnrat
      exact (not_le_of_gt hneg) hnonneg
    · simp only [hm, reduceIte]
      rw [show PowerSeries.coeff m.natAbs z = l.coeff (m.natAbs : ℤ) by
        simp [z]]
      congr 1
      exact (Int.eq_natAbs_of_nonneg (le_of_not_gt hm)).symm
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change puiseux_powerSeriesLevelHom n hn z = (x : HahnSeries Rat K)
  rw [puiseux_powerSeriesLevelHom_apply, hz]
  exact puiseux_levelHom_pullback hn (x : HahnSeries Rat K) hx

theorem puiseux_common_level_finset {K α : Type*} [Field K]
    (s : Finset α) (x : α → HahnSeries Rat K)
    (hx : ∀ i ∈ s, puiseuxBounded (x i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i ∈ s, puiseuxAtLevel n (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨n, hn, hsn⟩ := ih fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
      obtain ⟨m, hm, ham⟩ := hx a (Finset.mem_insert_self a s)
      refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact puiseux_atLevel_mul_denominator hm hn ham
      · simpa [Nat.mul_comm] using
          puiseux_atLevel_mul_denominator hn hm (hsn i hi)

theorem puiseux_polynomial_common_level {K : Type*} [Field K]
    (p : (HahnSeries Rat K)[X])
    (hp : ∀ i, puiseuxBounded (p.coeff i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, puiseuxAtLevel n (p.coeff i) := by
  obtain ⟨n, hn, hs⟩ :=
    puiseux_common_level_finset p.support (fun i ↦ p.coeff i)
      (fun i _ ↦ hp i)
  refine ⟨n, hn, fun i ↦ ?_⟩
  by_cases hi : i ∈ p.support
  · exact hs i hi
  · rw [Polynomial.notMem_support_iff.mp hi]
    intro r hr
    exact (hr rfl).elim

end
end MetaMathlibExt
end MetaMathlibExt
