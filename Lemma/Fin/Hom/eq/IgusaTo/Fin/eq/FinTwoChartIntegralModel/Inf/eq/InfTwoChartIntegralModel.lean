import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Scheme.IgusaScheme
import Lemma.Scheme.TwoChartIntegralModel
import Lemma.Int.P2MUtil

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve Scheme.IgusaScheme Scheme

/--
[ModularCurve_IgusaScheme_nonempty_iso_twoChartIntegralModel](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_IgusaScheme_nonempty_iso_twoChartIntegralModel.lean)
-/
@[path]
private lemma main
  {N : ℕ} [NeZero N]
  {ℓ : ℕ} [Fact ℓ.Prime] :
-- imply
  ∃ e : Scheme.IgusaScheme N ℓ ≅
    Scheme.TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) (jFull N),
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase _ _ _ = igusaTo N ℓ ∧
      ιFin N ℓ ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιFin _ _ _ ∧
      ιInf N ℓ ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιInf _ _ _ := by
-- proof
  refine ⟨Iso.refl _, ?_, ?_, ?_⟩
  · exact (Category.id_comp _).trans rfl
  · exact (Category.comp_id _).trans rfl
  · exact (Category.comp_id _).trans rfl


-- created on 2026-10-23
