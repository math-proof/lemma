import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.Lemma11_5
open MvPolynomial MeasureTheory Complex Real Set Metric DifferentialOperators
open scoped SchwartzMap


namespace DifferentialOperators

/--
[dbarFundSolDist_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
lemma dbarFundSolDist_apply
  {φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)} :
-- imply
  dbarFundSolDist φ = ∫ v, φ v * cauchyRiemannKernel v := by
-- proof
  rfl

end DifferentialOperators

namespace DifferentialOperators

/--
[dbarFundSolDist_eq_cauchyRiemannDistribution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
lemma dbarFundSolDist_eq_cauchyRiemannDistribution
-- imply
  dbarFundSolDist = cauchyRiemannDistribution := by
-- proof
  ext φ
  simp only [dbarFundSolDist_apply, cauchyRiemannDistribution_apply]
  simp only [smul_eq_mul]

end DifferentialOperators

namespace DifferentialOperators

/--
[dbar_dbarFundSol_eq_delta](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
lemma dbar_dbarFundSol_eq_delta
-- imply
  dbarOp dbarFundSolDist = TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin 2)) := by
-- proof
  rwa [dbarFundSolDist_eq_cauchyRiemannDistribution]

end DifferentialOperators

namespace DifferentialOperators

/--
[dbarFundSolDist_isFundSol](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
lemma dbarFundSolDist_isFundSol
-- imply
  IsTemperedFundamentalSolution 2 dbarPoly dbarFundSolDist :=
-- proof
  dbar_dbarFundSol_eq_delta
end DifferentialOperators


/--
[norm_complex_eq_euclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
private lemma norm_complex_eq_euclidean_eq
  {v : EuclideanSpace ℝ (Fin 2)} :
-- imply
  ‖(↑(v 0) + I * ↑(v 1) : ℂ)‖ = ‖v‖ := by
-- proof
  apply DifferentialOperators.norm_complex_eq_euclidean v

/--
[norm_cauchyRiemannKernel_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
private lemma norm_cauchyRiemannKernel_eq_eq
  {v : EuclideanSpace ℝ (Fin 2)} :
-- imply
  ‖cauchyRiemannKernel v‖ = (2 * Real.pi)⁻¹ * ‖v‖⁻¹ := by
-- proof
  apply DifferentialOperators.norm_cauchyRiemannKernel_eq v

/--
[norm_cauchyRiemannKernel_le_of_one_le_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
private lemma norm_cauchyRiemannKernel_le_of_one_le_norm_eq
  {v : EuclideanSpace ℝ (Fin 2)}
-- given
  (hv : 1 ≤ ‖v‖) :
-- imply
  ‖cauchyRiemannKernel v‖ ≤ (2 * Real.pi)⁻¹ := by
-- proof
  apply DifferentialOperators.norm_cauchyRiemannKernel_le_of_one_le_norm v hv

/--
[integrable_schwartz_mul_cauchyRiemannKernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
private lemma integrable_schwartz_mul_cauchyRiemannKernel_eq
  {φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)} :
-- imply
  Integrable (fun v => φ v * cauchyRiemannKernel v) := by
-- proof
  apply DifferentialOperators.integrable_schwartz_mul_cauchyRiemannKernel φ

/--
[norm_integral_schwartz_cauchyRiemannKernel_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean)
-/
@[path]
private lemma norm_integral_schwartz_cauchyRiemannKernel_le_eq :
-- imply
  ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ), ‖∫ v, φ v * cauchyRiemannKernel v‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2)) ℂ)) φ := by
-- proof
  apply DifferentialOperators.norm_integral_schwartz_cauchyRiemannKernel_le


-- created on 2026-10-23
