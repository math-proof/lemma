import Mathlib
import sympy.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW


/--
[sw_solution_bochner_constrains_fields](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWNonVacuousVerification.lean)
-/
@[path]
lemma sw_solution_bochner_constrains_fields
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc} :
-- imply
  (sol.scalarCurvatureVal / 4) * sol.supNormSq + (1/4) * sol.supNormSq ^ 2 ≤ 0 := by
-- proof
  have h1 := sol.laplacianTerm_nonneg
  have h2 := sol.covDerivNormSq_nonneg
  have h3 := sol.bochner_eq
  linarith

/--
[sw_solution_positive_scalar_forces_reducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWNonVacuousVerification.lean)
-/
@[path]
lemma sw_solution_positive_scalar_forces_reducible
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc}
-- given
  (hs : sol.scalarCurvatureVal > 0) :
-- imply
  sol.supNormSq = 0 := by
-- proof
  have hbound := sw_solution_bochner_constrains_fields sol
  have hnn := sol.supNormSq_nonneg
  by_contra h
  push Not at h
  have hpos : sol.supNormSq > 0 := lt_of_le_of_ne hnn (Ne.symm h)
  have h1 : (sol.scalarCurvatureVal / 4) * sol.supNormSq > 0 := by positivity
  have h2 : (1/4 : ℝ) * sol.supNormSq ^ 2 ≥ 0 := by positivity
  linarith

/--
[sw_solution_positive_scalar_is_reducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWNonVacuousVerification.lean)
-/
@[path]
lemma sw_solution_positive_scalar_is_reducible
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc}
-- given
  (hs : sol.scalarCurvatureVal > 0) :
-- imply
  sol.isReducible := by
-- proof
  exact (sol.isReducible_iff_supNormSq_zero).mpr
    (sw_solution_positive_scalar_forces_reducible sol hs)
end HasGaugeActionNonVacuous
section CrossStructureConsistency
end CrossStructureConsistency


-- created on 2026-10-23
