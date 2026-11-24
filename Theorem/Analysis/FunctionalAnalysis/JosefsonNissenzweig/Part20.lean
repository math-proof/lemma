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
public import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part21


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_stableBlockingChain_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    jnStableBlockingChain hz (k + 1) =
      jnBlockingComp (jnStableBlockingChain hz k) (jnStableStepBlocking hz k) := by
  rfl

theorem jn_stableBlockingChain_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (n : ℕ) :
    jnStableBlockingChain hz n = jnBlockingChain (jnStableStepBlocking hz) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [jn_stableBlockingChain_succ, jnBlockingChain, ih]

theorem jn_stableBlockingChain_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k d : ℕ) :
    jnStableBlockingChain hz (k + d) =
      jnBlockingComp (jnStableBlockingChain hz k)
        (jnBlockingTailChain (jnStableStepBlocking hz) k d) := by
  rw [jn_stableBlockingChain_eq, jn_stableBlockingChain_eq,
    jn_blockingChain_add]

theorem jn_log2_monotone : Monotone Nat.log2 := by
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  · have hn : n ≠ 0 := by omega
    exact (Nat.le_log2 hn).2 ((Nat.log2_self_le hm).trans hmn)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
