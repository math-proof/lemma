import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierKernelClosedForm
open StatMech StatMech.FrontierD


/--
[tsum_exp_cos_succ_eq_poisson](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierKernelClosedForm.lean)
-/
@[path]
private lemma tsum_exp_cos_succ_eq_poisson_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∑' n : Nat, Real.exp (-lam) ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha)) = let r := Real.exp (-lam) (r * Real.cos alpha - r ^ 2) / (1 - 2 * r * Real.cos alpha + r ^ 2) := by
-- proof
  apply StatMech.FrontierD.tsum_exp_cos_succ_eq_poisson hlam alpha

/--
[sixVertexXiFourier_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierKernelClosedForm.lean)
-/
@[path]
private lemma sixVertexXiFourier_eq_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexXiFourier lam alpha = Real.sinh lam / (Real.cosh lam - Real.cos alpha) := by
-- proof
  apply StatMech.FrontierD.sixVertexXiFourier_eq hlam alpha


-- created on 2026-10-23
