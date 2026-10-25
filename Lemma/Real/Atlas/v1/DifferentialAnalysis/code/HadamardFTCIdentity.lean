import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.HadamardFTCIdentity
open MeasureTheory HadamardDecomposition
open scoped SchwartzMap


namespace HadamardDecomposition

/--
[continuous_fderiv_comp_smul_path](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HadamardFTCIdentity.lean)
-/
@[path]
lemma continuous_fderiv_comp_smul_path
  {n : ℕ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
  {x v : EuclideanSpace ℝ (Fin n)} :
-- imply
  Continuous (fun t : ℝ => fderiv ℝ (⇑φ) (t • x) v) := by
-- proof
  have h1 : Continuous (⇑(SchwartzMap.fderivCLM ℝ
    (EuclideanSpace ℝ (Fin n)) ℂ φ)) :=
    (SchwartzMap.fderivCLM ℝ _ ℂ φ).continuous
  have h2 : Continuous (fun t : ℝ => t • x) :=
    continuous_id.smul continuous_const
  have h3 : Continuous (fun t : ℝ => (⇑(SchwartzMap.fderivCLM ℝ _ ℂ φ)) (t • x)) :=
    h1.comp h2
  exact h3.clm_apply continuous_const

end HadamardDecomposition


-- created on 2026-10-23
