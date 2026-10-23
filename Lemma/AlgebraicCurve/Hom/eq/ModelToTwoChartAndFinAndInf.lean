import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Lemma.Definitions.Def_ModularCurve_TwoChartModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


/-- ported from external source -/
@[path]
private lemma main
  {A : Type u} [CommRing A]
  {K : Type u} [Field K] [Algebra A K]
  {j : K} [Fact (j ≠ 0)] :
-- imply
  ∃ e : ModularCurve.TwoChartModel A K j ≅ AlgebraicCurve.TwoChartIntegralModel A K j,
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A K j = ModularCurve.TwoChart.modelTo A K j ∧
      ModularCurve.TwoChart.ιFin A K j ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιFin A K j ∧
      ModularCurve.TwoChart.ιInf A K j ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιInf A K j :=
-- proof
  ⟨Iso.refl _, Category.id_comp _, Category.comp_id _, Category.comp_id _⟩


-- created on 2026-10-23
