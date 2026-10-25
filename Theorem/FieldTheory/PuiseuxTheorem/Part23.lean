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
import Def.FieldTheory.PuiseuxTheorem.Part25
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_level_decomposition {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (y : ↥(puiseuxLevelField K n hn)) :
    let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
      puiseux_levelAlgebra n hn
    ∃ z : LaurentSeries K, puiseux_levelHom n hn z = (y : HahnSeries Rat K) ∧
      y = ∑ r : Fin n, puiseux_residuePart hn r z • puiseux_levelGenerator hn r := by
  let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_levelAlgebra n hn
  obtain ⟨z, hz⟩ := (RingHom.mem_fieldRange.mp y.property)
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  change (puiseuxLevelField K n hn).subtype y =
    (puiseuxLevelField K n hn).subtype
      (∑ r : Fin n, puiseux_residuePart hn r z • puiseux_levelGenerator hn r)
  rw [map_sum]
  simp only [Algebra.smul_def, map_mul]
  change (y : HahnSeries Rat K) =
    ∑ r : Fin n,
      ((algebraMap (LaurentSeries K) ↥(puiseuxLevelField K n hn)
        (puiseux_residuePart hn r z) : ↥(puiseuxLevelField K n hn)) : HahnSeries Rat K) *
      ((puiseux_levelGenerator (K := K) hn r : ↥(puiseuxLevelField K n hn)) :
        HahnSeries Rat K)
  have halg (a : LaurentSeries K) :
      ((algebraMap (LaurentSeries K) ↥(puiseuxLevelField K n hn) a :
        ↥(puiseuxLevelField K n hn)) : HahnSeries Rat K) = puiseux_laurentHom a := rfl
  have hgen (r : Fin n) :
      ((puiseux_levelGenerator (K := K) hn r : ↥(puiseuxLevelField K n hn)) :
        HahnSeries Rat K) =
        puiseux_levelHom n hn (HahnSeries.single ((r : ℕ) : ℤ) 1) := rfl
  simp_rw [halg, hgen]
  rw [← hz]
  calc
    puiseux_levelHom n hn z =
        puiseux_levelHom n hn
          (∑ r : Fin n, puiseux_scaleHom n hn (puiseux_residuePart hn r z) *
            HahnSeries.single ((r : ℕ) : ℤ) 1) :=
      congrArg (puiseux_levelHom n hn) (puiseux_residue_decomposition hn z).symm
    _ = _ := by simp only [map_sum, map_mul, puiseux_levelHom_scaleHom]

theorem puiseux_level_module_finite {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) :
    @Module.Finite (LaurentSeries K) ↥(puiseuxLevelField K n hn) inferInstance inferInstance
      (puiseux_levelAlgebra n hn).toModule := by
  let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_levelAlgebra n hn
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range (puiseux_levelGenerator (K := K) hn), Set.finite_range _, ?_⟩
  apply top_unique
  intro y _
  obtain ⟨z, _, hy⟩ := puiseux_level_decomposition hn y
  rw [hy]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self r))

end
end MetaMathlibExt
end MetaMathlibExt
