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
import Def.FieldTheory.PuiseuxTheorem.Part23
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_scaleHom_apply {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) :
    puiseux_scaleHom n hn x = HahnSeries.embDomain (puiseux_scaleIndexEmbedding n hn) x :=
  rfl

theorem puiseux_index_scale {n : ℕ} (hn : 0 < n) (m : ℤ) :
    puiseux_indexEmbedding n hn (puiseux_scaleIndexEmbedding n hn m) =
      puiseux_indexEmbedding 1 (by norm_num) m := by
  rw [puiseux_scaleIndexEmbedding_apply, puiseux_indexEmbedding_apply,
    puiseux_indexEmbedding_apply]
  push_cast
  field_simp [hn.ne']

theorem puiseux_index_one_range_subset {n : ℕ} (hn : 0 < n) :
    Set.range (puiseux_indexEmbedding 1 (by norm_num)) ⊆
      Set.range (puiseux_indexEmbedding n hn) := by
  rintro _ ⟨m, rfl⟩
  exact ⟨puiseux_scaleIndexEmbedding n hn m, puiseux_index_scale hn m⟩

theorem puiseux_scale_mem_range_of_index_mem_one {n : ℕ} (hn : 0 < n) (a : ℤ)
    (ha : puiseux_indexEmbedding n hn a ∈
      Set.range (puiseux_indexEmbedding 1 (by norm_num))) :
    a ∈ Set.range (puiseux_scaleIndexEmbedding n hn) := by
  obtain ⟨m, hm⟩ := ha
  refine ⟨m, (puiseux_indexEmbedding n hn).injective ?_⟩
  rw [puiseux_index_scale]
  exact hm

theorem puiseux_levelHom_scaleHom {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) :
    puiseux_levelHom n hn (puiseux_scaleHom n hn x) = puiseux_laurentHom x := by
  rw [show puiseux_laurentHom x = puiseux_levelHom 1 (by norm_num) x from rfl]
  ext r
  by_cases hr : r ∈ Set.range (puiseux_indexEmbedding n hn)
  · obtain ⟨a, rfl⟩ := hr
    rw [puiseux_levelHom_apply, HahnSeries.embDomain_coeff, puiseux_scaleHom_apply]
    by_cases ha : a ∈ Set.range (puiseux_scaleIndexEmbedding n hn)
    · obtain ⟨m, rfl⟩ := ha
      rw [HahnSeries.embDomain_coeff, puiseux_index_scale, puiseux_levelHom_apply,
        HahnSeries.embDomain_coeff]
    · rw [HahnSeries.embDomain_of_notMem_range ha, puiseux_levelHom_apply,
        HahnSeries.embDomain_of_notMem_range]
      exact fun h ↦ ha (puiseux_scale_mem_range_of_index_mem_one hn a h)
  · rw [puiseux_levelHom_apply,
      HahnSeries.embDomain_of_notMem_range (f := puiseux_indexEmbedding n hn) hr,
      puiseux_levelHom_apply, HahnSeries.embDomain_of_notMem_range]
    exact fun h ↦ hr (puiseux_index_one_range_subset hn h)

end
end MetaMathlibExt
end MetaMathlibExt
