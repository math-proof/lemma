import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SWModuliQuotient


/--
[SWModuliQuotient.mk_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliQuotient.lean)
-/
@[path]
lemma SWModuliQuotient.mk_surjective
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {gd : GaugeActionData spinc} :
-- imply
  Function.Surjective (SWModuliQuotient.mk gd) := by
-- proof
  intro q
  induction q using Quotient.ind with
  | _ sol => exact ⟨sol, rfl⟩

/--
[SWModuliQuotient.supNormSq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliQuotient.lean)
-/
@[path]
lemma SWModuliQuotient.supNormSq_nonneg
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {gd : GaugeActionData spinc}
  {q : SWModuliQuotient gd} :
-- imply
  0 ≤ SWModuliQuotient.supNormSq gd q := by
-- proof
  induction q using Quotient.ind with
  | _ sol => exact sol.supNormSq_nonneg

/--
[SWModuliQuotient.no_reducibles_generic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliQuotient.lean)
-/
@[path]
lemma SWModuliQuotient.no_reducibles_generic
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
  [CompactSpace M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  [htop : Has4ManifoldTopology M]
  {spinc : SpinCStructure M Ω1 Ω2}
  {gd : GaugeActionData spinc}
  [hgeneric : IsGenericPair spinc]
  {sol : SWSolution spinc}
-- given
  (hb₂_pos : htop.Q.b₂_plus ≥ 1) :
-- imply
  ¬(SWModuliQuotient.IsReducible gd (SWModuliQuotient.mk gd sol)) := by
-- proof
  intro hred
  have h_no_red := IsGenericPair.no_reducible_solutions hb₂_pos sol
  exact h_no_red ((sol.isReducible_iff_supNormSq_zero).mpr hred)
/-- Dimension formula for the SW moduli space:
$4d = c_1(L)^2 - (2\chi(M) + 3\sigma(M))$ for some integer $d \in \mathbb{Z}$. -/


-- created on 2026-10-23
