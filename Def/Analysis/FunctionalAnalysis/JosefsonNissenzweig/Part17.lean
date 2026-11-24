module
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
public import Theorem.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
public import Theorem.Set.Any_All_Any_All_LtNormSubOrHasUniformL1LowerBound.of.IsBounded_Range
public import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part13
public import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part15


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnBoundedEval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R) : E →L[ℝ] JnBoundedSeq := by
  let F : E → JnBoundedSeq := fun x =>
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun n => (z n) x) (R * ‖x‖) (fun n => by
        exact (ContinuousLinearMap.le_opNorm (z n) x).trans
          (mul_le_mul_of_nonneg_right (hz n) (norm_nonneg x)))
  let f : E →ₗ[ℝ] JnBoundedSeq :=
    { toFun := F
      map_add' := fun x y => by
        ext n
        simp only [F, BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete,
          map_add, BoundedContinuousFunction.add_apply]
      map_smul' := fun c x => by
        ext n
        simp only [F, BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete,
          map_smul, BoundedContinuousFunction.smul_apply, RingHom.id_apply] }
  exact f.mkContinuous R fun x => by
    apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    · exact mul_nonneg (le_trans (norm_nonneg (z 0)) (hz 0)) (norm_nonneg x)
    · intro n
      exact (ContinuousLinearMap.le_opNorm (z n) x).trans
        (mul_le_mul_of_nonneg_right (hz n) (norm_nonneg x))

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
