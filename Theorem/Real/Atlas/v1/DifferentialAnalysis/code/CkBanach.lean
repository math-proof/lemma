module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.v1.Atlas.DifferentialAnalysis.code.CkBanach.Part2
open Filter Topology Finset TestFunctions
open scoped ZeroAtInfty


public section

namespace TestFunctions

/--
[ContDiffZeroAtInfty.differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean)
-/
@[path]
theorem ContDiffZeroAtInfty.differentiable
  {n : ℕ}
  {u : ContDiffZeroAtInfty n} :
-- imply
  Differentiable ℝ (⇑u.toZeroAtInftyContinuousMap) :=
-- proof
  u.contDiff_one.differentiable (by norm_num)

end TestFunctions

/--
[ContDiffZeroAtInfty.toC0_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean)
-/
@[path]
private theorem toC0_injective_eq
  {n : ℕ} :
-- imply
  Function.Injective (ContDiffZeroAtInfty.toZeroAtInftyContinuousMap (n := n)) := by
-- proof
  apply TestFunctions.ContDiffZeroAtInfty.toC0_injective

/--
[tendsto_partialDeriv_of_fderiv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean)
-/
@[path]
private theorem tendsto_partialDeriv_of_fderiv_eq_eq
  {n : ℕ}
  {f : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ}
  {g : Fin n → EuclideanSpace ℝ (Fin n) → ℂ}
  {j : Fin n}
-- given
  (heq : ∀ j x, fderiv ℝ (⇑f) x (EuclideanSpace.single j 1) = g j x)
  (htend : ∀ j, Tendsto (g j) (cocompact _) (𝓝 0)) :
-- imply
  Tendsto (fun x => fderiv ℝ (⇑f) x (EuclideanSpace.single j 1)) (cocompact _) (𝓝 0) := by
-- proof
  apply TestFunctions.tendsto_partialDeriv_of_fderiv_eq f g heq htend j

/--
[ContDiffZeroAtInfty.norm_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean)
-/
@[path]
private theorem norm_def_eq
  {n : ℕ}
  {u : ContDiffZeroAtInfty n} :
-- imply
  ‖u‖ = (⨆ x, ‖u.toZeroAtInftyContinuousMap x‖) + ∑ j : Fin n, ⨆ x, ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖ := by
-- proof
  apply TestFunctions.ContDiffZeroAtInfty.norm_def u

/--
[ContDiffZeroAtInfty.c1_norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean)
-/
@[path]
private theorem c1_norm_nonneg_eq
  {n : ℕ}
  {u : ContDiffZeroAtInfty n} :
-- imply
  0 ≤ ‖u‖ := by
-- proof
  apply TestFunctions.ContDiffZeroAtInfty.c1_norm_nonneg u

/--
[ContDiffZeroAtInfty.c1_norm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean)
-/
@[path]
private theorem c1_norm_zero_eq
  {n : ℕ} :
-- imply
  ‖(0 : ContDiffZeroAtInfty n)‖ = 0 := by
-- proof
  apply TestFunctions.ContDiffZeroAtInfty.c1_norm_zero


-- created on 2026-10-23
