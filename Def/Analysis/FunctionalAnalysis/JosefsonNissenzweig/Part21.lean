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
import Structure.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part2


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
