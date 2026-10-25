import Mathlib
import sympy.Basic
import Lemma.ModularCurve.TwoChartModel
import Lemma.AlgebraicCurve.TwoChartIntegralModel

namespace Definitions
end Definitions
open Definitions
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

/--
[ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo.lean)
-/
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
-- updated on 2026-10-24
