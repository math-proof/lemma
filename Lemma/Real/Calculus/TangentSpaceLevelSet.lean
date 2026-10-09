import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.TangentSpaceLevelSet

open Real.Calculus.TangentSpaceLevelSet
open scoped Topology

/--
[levelSet_tangent_vel_of_curve](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/TangentSpaceLevelSet.lean)
-/
@[path]
private lemma levelSet_tangent_vel_of_curve_eq
-- given
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {c : ℝ} {x v : E}
  (hf : DifferentiableAt ℝ f x)
  {γ : ℝ → E} (hγ0 : γ 0 = x) (hγ : HasDerivAt γ v 0)
  (hmem : ∀ t, f (γ t) = c) :
-- imply
  fderiv ℝ f x v = 0 := by
-- proof
  apply levelSet_tangent_vel_of_curve hf hγ0 hγ hmem


/--
[HasStrictFDerivAt.exists_levelSet_curve](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/TangentSpaceLevelSet.lean)
-/
@[path]
private lemma HasStrictFDerivAt.exists_levelSet_curve_eq
-- given
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x v : E}
  (hf : HasStrictFDerivAt f f' x) (hsurj : Function.Surjective f')
  (hmem : f' v = 0) :
-- imply
  ∃ φ : ℝ → E, φ 0 = x ∧ HasDerivAt φ v 0 ∧ ∀ᶠ t in 𝓝 0, f (φ t) = f x := by
-- proof
  apply HasStrictFDerivAt.exists_levelSet_curve hf hsurj hmem


/--
[levelSet_curve_of_tangent_vel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/TangentSpaceLevelSet.lean)
-/
@[path]
private lemma levelSet_curve_of_tangent_vel_eq
-- given
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {c : ℝ} {x v : E}
  (hf : ContDiff ℝ 1 f) (hx : f x = c)
  (hsurj : Function.Surjective (fderiv ℝ f x))
  (hmem : fderiv ℝ f x v = 0) :
-- imply
  ∃ γ : ℝ → E, γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ t, f (γ t) = c := by
-- proof
  apply levelSet_curve_of_tangent_vel hf hx hsurj hmem


-- created on 2026-10-09
