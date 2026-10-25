/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
import Lemma.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
import Lemma.Set.Any_All_Any_All_LtNormSubOrHasUniformL1LowerBound.of.IsBounded_Range
import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part13
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part23


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_l1SignLinearMap_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m : ℕ)
    (y : Submodule.span ℝ (Set.range x)) :
    ‖jnL1SignLinearMap hc hx m y‖ ≤ c⁻¹ * ‖y‖ := by
  let b := jnL1Basis hc hx
  let a : ℕ →₀ ℝ := b.repr y
  have hcomb : Finsupp.linearCombination ℝ x a = (y : E) := by
    have hsub : b.repr.symm a = y := b.repr.symm_apply_apply y
    have hval := congrArg Subtype.val hsub
    rw [Finsupp.linearCombination_apply]
    calc
      a.sum (fun i t => t • x i) = a.sum (fun i t => t • (b i : E)) := by
        apply Finsupp.sum_congr
        intro i hi
        simp only [b, jnL1Basis, Module.Basis.coe_span_apply]
      _ = ((a.sum (fun i t => t • b i) : Submodule.span ℝ (Set.range x)) : E) := by
        exact (map_finsuppSum (Submodule.span ℝ (Set.range x)).subtype a
          (fun i t => t • b i)).symm
      _ = (y : E) := by
        simpa only [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply] using hval
  have hsum : a.sum (fun _ t => |t|) ≤ c⁻¹ * ‖y‖ := by
    apply (le_inv_mul_iff₀ hc).mpr
    simpa only [hcomb, Submodule.norm_coe] using hx a
  calc
    ‖jnL1SignLinearMap hc hx m y‖ =
        |a.sum (fun i t => t * jnRademacher i m)| := by
      simp only [Real.norm_eq_abs, jnL1SignLinearMap, Module.Basis.constr_apply, a,
        b, smul_eq_mul]
    _ ≤ a.sum (fun _ t => |t|) := by
      rw [Finsupp.sum, Finsupp.sum]
      calc
        |∑ i ∈ a.support, a i * jnRademacher i m| ≤
            ∑ i ∈ a.support, |a i * jnRademacher i m| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ a.support, |a i| := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [abs_mul, jn_rademacher_apply, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    _ ≤ c⁻¹ * ‖y‖ := hsum

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
