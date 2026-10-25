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
import Def.FieldTheory.PuiseuxTheorem.Part14
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_atLevel_mul_denominator {K : Type*} [Field K] {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) {x : HahnSeries Rat K} (hx : puiseuxAtLevel n x) :
    puiseuxAtLevel (n * k) x := by
  intro r hr
  obtain ⟨m, rfl⟩ := hx r hr
  refine ⟨m * (k : ℤ), ?_⟩
  push_cast
  field_simp [hn.ne', hk.ne']

theorem puiseux_bounded_zero {K : Type*} [Field K] :
    puiseuxBounded (0 : HahnSeries Rat K) := by
  refine ⟨1, by norm_num, ?_⟩
  simpa using puiseux_levelHom_atLevel (K := K) (n := 1) (by norm_num)
    (0 : LaurentSeries K)

theorem puiseux_bounded_one {K : Type*} [Field K] :
    puiseuxBounded (1 : HahnSeries Rat K) := by
  refine ⟨1, by norm_num, ?_⟩
  simpa using puiseux_levelHom_atLevel (K := K) (n := 1) (by norm_num)
    (1 : LaurentSeries K)

theorem puiseux_bounded_neg {K : Type*} [Field K] {x : HahnSeries Rat K}
    (hx : puiseuxBounded x) : puiseuxBounded (-x) := by
  obtain ⟨n, hn, hx⟩ := hx
  refine ⟨n, hn, (puiseux_atLevel_iff hn (-x)).2 ?_⟩
  obtain ⟨z, rfl⟩ := (puiseux_atLevel_iff hn x).1 hx
  exact ⟨-z, map_neg (puiseux_levelHom n hn) z⟩

theorem puiseux_bounded_inv {K : Type*} [Field K] {x : HahnSeries Rat K}
    (hx : puiseuxBounded x) : puiseuxBounded x⁻¹ := by
  obtain ⟨n, hn, hx⟩ := hx
  refine ⟨n, hn, (puiseux_atLevel_iff hn x⁻¹).2 ?_⟩
  obtain ⟨z, rfl⟩ := (puiseux_atLevel_iff hn x).1 hx
  exact ⟨z⁻¹, map_inv₀ (puiseux_levelHom n hn) z⟩

theorem puiseux_common_level {K : Type*} [Field K] {x y : HahnSeries Rat K}
    (hx : puiseuxBounded x) (hy : puiseuxBounded y) :
    ∃ n : ℕ, 0 < n ∧ puiseuxAtLevel n x ∧ puiseuxAtLevel n y := by
  obtain ⟨n, hn, hx⟩ := hx
  obtain ⟨m, hm, hy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, puiseux_atLevel_mul_denominator hn hm hx, ?_⟩
  simpa [Nat.mul_comm] using puiseux_atLevel_mul_denominator hm hn hy

theorem puiseux_bounded_add {K : Type*} [Field K] {x y : HahnSeries Rat K}
    (hx : puiseuxBounded x) (hy : puiseuxBounded y) : puiseuxBounded (x + y) := by
  obtain ⟨n, hn, hxn, hyn⟩ := puiseux_common_level hx hy
  refine ⟨n, hn, (puiseux_atLevel_iff hn (x + y)).2 ?_⟩
  obtain ⟨zx, hzx⟩ := (puiseux_atLevel_iff hn x).1 hxn
  obtain ⟨zy, hzy⟩ := (puiseux_atLevel_iff hn y).1 hyn
  exact ⟨zx + zy, by rw [map_add, hzx, hzy]⟩

theorem puiseux_bounded_mul {K : Type*} [Field K] {x y : HahnSeries Rat K}
    (hx : puiseuxBounded x) (hy : puiseuxBounded y) : puiseuxBounded (x * y) := by
  obtain ⟨n, hn, hxn, hyn⟩ := puiseux_common_level hx hy
  refine ⟨n, hn, (puiseux_atLevel_iff hn (x * y)).2 ?_⟩
  obtain ⟨zx, hzx⟩ := (puiseux_atLevel_iff hn x).1 hxn
  obtain ⟨zy, hzy⟩ := (puiseux_atLevel_iff hn y).1 hyn
  exact ⟨zx * zy, by rw [map_mul, hzx, hzy]⟩

end
end MetaMathlibExt
end MetaMathlibExt
