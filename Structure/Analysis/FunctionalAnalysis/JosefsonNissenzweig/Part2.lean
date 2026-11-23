/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

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
public import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part19


public section

section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

structure JnStableRademacherStep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (z : ℕ → StrongDual ℝ E) (k : ℕ) where
  x : E
  u : ℕ → ℕ
  norm_le : ‖x‖ ≤ 1
  strictMono : StrictMono u
  good : ∀ n, δ ≤ jnBlockApply (jnRademacherBlocking k) z (u n) x

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
