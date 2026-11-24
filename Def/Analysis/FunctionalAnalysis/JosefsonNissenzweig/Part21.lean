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
public import Structure.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnStableRademacherStepData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    JnStableRademacherStep δ z k := by
  let h := jn_stable_rademacher_step hz k
  let x := Classical.choose h
  let hrest := Classical.choose_spec h
  let u := Classical.choose hrest
  let hprops := Classical.choose_spec hrest
  exact ⟨x, u, hprops.1, hprops.2.1, hprops.2.2⟩

noncomputable def jnStableBlockingChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) :
    ℕ → JnBlocking
  | 0 => jnIdBlocking
  | k + 1 =>
      let base := jnStableBlockingChain hz k
      let data := jnStableRademacherStepData (jn_blockStable_blockApply hz base) k
      jnBlockingComp base
        (jnWholeGroupBlocking (2 ^ (k + 1)) (by positivity) data.u data.strictMono)

noncomputable def jnStableStageData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    JnStableRademacherStep δ (jnBlockApply (jnStableBlockingChain hz k) z) k :=
  jnStableRademacherStepData
    (jn_blockStable_blockApply hz (jnStableBlockingChain hz k)) k

noncomputable def jnStableStepBlocking
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    JnBlocking :=
  jnWholeGroupBlocking (2 ^ (k + 1)) (by positivity)
    (jnStableStageData hz k).u (jnStableStageData hz k).strictMono

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
