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
public import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_blockApply_comp
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a b : JnBlocking) (x : ℕ → E) (n : ℕ) :
    jnBlockApply (jnBlockingComp a b) x n =
      jnBlockApply b (jnBlockApply a x) n := by
  exact Finsupp.linearCombination_linearCombination ℝ x a.coeff (b.coeff n)

theorem jn_blockApply_comp_fun
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a b : JnBlocking) (x : ℕ → E) :
    jnBlockApply (jnBlockingComp a b) x =
      jnBlockApply b (jnBlockApply a x) := by
  funext n
  exact jn_blockApply_comp a b x n

theorem jnBlocking_ext {a b : JnBlocking}
    (h : ∀ n, a.coeff n = b.coeff n) : a = b := by
  cases a with
  | mk ac an as =>
      cases b with
      | mk bc bn bs =>
          dsimp at h
          have hab : ac = bc := funext h
          subst bc
          rfl

theorem jn_blockingComp_assoc (a b c : JnBlocking) :
    jnBlockingComp (jnBlockingComp a b) c =
      jnBlockingComp a (jnBlockingComp b c) := by
  apply jnBlocking_ext
  intro n
  exact (Finsupp.linearCombination_linearCombination ℝ a.coeff b.coeff
    (c.coeff n)).symm

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
