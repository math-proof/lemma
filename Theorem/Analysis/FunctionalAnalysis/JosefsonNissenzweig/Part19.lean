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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part20


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_blockStable_blockApply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z)
    (a : JnBlocking) : JnBlockStable δ (jnBlockApply a z) := by
  intro b
  obtain ⟨x, hx, hcofinal⟩ := hz (jnBlockingComp a b)
  refine ⟨x, hx, fun N => ?_⟩
  obtain ⟨n, hn, hgood⟩ := hcofinal N
  refine ⟨n, hn, ?_⟩
  rw [jn_blockApply_comp] at hgood
  exact hgood

theorem jn_stable_rademacher_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    ∃ (x : E) (u : ℕ → ℕ), ‖x‖ ≤ 1 ∧ StrictMono u ∧
      ∀ n, δ ≤ jnBlockApply (jnRademacherBlocking k) z (u n) x := by
  classical
  obtain ⟨x, hx, hcofinal⟩ := hz (jnRademacherBlocking k)
  let a : ℕ → ℝ := fun n => jnBlockApply (jnRademacherBlocking k) z n x
  by_cases hpositive : ∀ N, ∃ n, N ≤ n ∧ δ ≤ a n
  · obtain ⟨u, hu, hgood⟩ := jn_exists_strictMono_of_cofinal _ hpositive
    exact ⟨x, u, hx, hu, hgood⟩
  · push Not at hpositive
    obtain ⟨N, hN⟩ := hpositive
    have hnegative : ∀ M, ∃ n, M ≤ n ∧ δ ≤ -a n := by
      intro M
      obtain ⟨n, hn, habs⟩ := hcofinal (max M N)
      have hnM : M ≤ n := (le_max_left _ _).trans hn
      have hnN : N ≤ n := (le_max_right _ _).trans hn
      refine ⟨n, hnM, ?_⟩
      change δ ≤ ‖a n‖ at habs
      have hlt : a n < δ := hN n hnN
      rcases le_total 0 (a n) with ha | ha
      · rw [Real.norm_eq_abs, abs_of_nonneg ha] at habs
        exact (not_lt_of_ge habs hlt).elim
      · simpa only [Real.norm_eq_abs, abs_of_nonpos ha] using habs
    obtain ⟨u, hu, hgood⟩ := jn_exists_strictMono_of_cofinal _ hnegative
    refine ⟨-x, u, by simpa using hx, hu, fun n => ?_⟩
    simpa only [map_neg] using hgood n

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
