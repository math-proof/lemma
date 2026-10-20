import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.LaplaceTransform.ExponentialBound
open MeasureTheory Set Real Filter Topology Asymptotics


/--
[laplaceConvergent_of_norm_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
private lemma laplaceConvergent_of_norm_le_exp_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {a C : ℝ}
  {s : ℂ}
-- given
  (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
  (hC : 0 ≤ C)
  (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t))
  (hs : a < s.re) :
-- imply
  LaplaceConvergent f s := by
-- proof
  apply laplaceConvergent_of_norm_le_exp f a C hf hC hbound hs

/--
[laplaceConvergent_of_isBigO_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
private lemma laplaceConvergent_of_isBigO_exp_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {a : ℝ}
  {s : ℂ}
-- given
  (hloc : LocallyIntegrableOn f (Set.Ici 0))
  (ho : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t)))
  (hs : a < s.re) :
-- imply
  LaplaceConvergent f s := by
-- proof
  apply laplaceConvergent_of_isBigO_exp f a hloc ho hs

/--
[differentiableOn_laplace_of_norm_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
private lemma differentiableOn_laplace_of_norm_le_exp_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℝ → E}
  {a C : ℝ}
-- given
  (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
  (hC : 0 ≤ C)
  (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)) :
-- imply
  DifferentiableOn ℂ (laplace f) {s | a < s.re} := by
-- proof
  apply differentiableOn_laplace_of_norm_le_exp f a C hf hC hbound

/--
[differentiableOn_laplace_of_isBigO_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
private lemma differentiableOn_laplace_of_isBigO_exp_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℝ → E}
  {a : ℝ}
-- given
  (hf : LocallyIntegrableOn f (Set.Ici 0))
  (hO : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t))) :
-- imply
  DifferentiableOn ℂ (laplace f) {s | a < s.re} := by
-- proof
  apply differentiableOn_laplace_of_isBigO_exp f a hf hO


-- created on 2026-10-20
