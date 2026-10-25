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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part22


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_stableBlockingChain_good
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z)
    (k d n : ℕ) :
    δ ≤ jnBlockApply (jnRademacherBlocking k)
      (jnBlockApply (jnStableBlockingChain hz (k + 1 + d)) z) n
      (jnStableStageData hz k).x := by
  induction d generalizing n with
  | zero =>
      rw [Nat.add_zero, jn_stableBlockingChain_succ, jn_blockApply_comp_fun]
      change δ ≤ jnBlockApply (jnRademacherBlocking k)
        (jnBlockApply
          (jnWholeGroupBlocking (2 ^ (k + 1)) (by positivity)
            (jnStableStageData hz k).u (jnStableStageData hz k).strictMono)
          (jnBlockApply (jnStableBlockingChain hz k) z)) n
        (jnStableStageData hz k).x
      rw [jn_blockApply_rademacherBlocking_wholeGroup (le_refl k)]
      simpa [jnWholeGroupIndex, Nat.mod_one] using (jnStableStageData hz k).good n
  | succ d ih =>
      let j := k + 1 + d
      have hindex : k + 1 + (d + 1) = j + 1 := by omega
      rw [hindex, jn_stableBlockingChain_succ, jn_blockApply_comp_fun]
      change δ ≤ jnBlockApply (jnRademacherBlocking k)
        (jnBlockApply
          (jnWholeGroupBlocking (2 ^ (j + 1)) (by positivity)
            (jnStableStageData hz j).u (jnStableStageData hz j).strictMono)
          (jnBlockApply (jnStableBlockingChain hz j) z)) n
        (jnStableStageData hz k).x
      rw [jn_blockApply_rademacherBlocking_wholeGroup (by omega)]
      exact ih (jnWholeGroupIndex (2 ^ (j - k)) (jnStableStageData hz j).u n)

theorem jn_stableDiagonal_good
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z)
    (k n : ℕ) (hn : 0 < n) :
    δ ≤ jnBlockApply (jnRademacherBlocking k)
      (jnBlockApply (jnStableDiagonalBlocking hz) z) n
      (jnStableStageData hz k).x := by
  rw [jn_rademacher_stableDiagonal_eq hz k n hn]
  have hnonzero : 2 ^ (k + 1) * n ≠ 0 := by positivity
  have hstage : k + 1 ≤ Nat.log2 (2 ^ (k + 1) * n) := by
    apply (Nat.le_log2 hnonzero).2
    exact Nat.le_mul_of_pos_right _ hn
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hstage
  rw [hd]
  exact jn_stableBlockingChain_good hz k d n

theorem jn_of_stable_block
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ R : ℝ} (hδ : 0 < δ) (z : ℕ → StrongDual ℝ E)
    (hzbound : ∀ n, ‖z n‖ ≤ R) (hz : JnBlockStable δ z) :
    ∃ (ψ : ℕ → StrongDual ℝ E), (∀ k, ‖ψ k‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun k => (ψ k) x) Filter.atTop (nhds (0 : ℝ)) := by
  obtain ⟨L, hpos, hone, hshift, _⟩ :=
    MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit
  let b := jnStableDiagonalBlocking hz
  let y : ℕ → StrongDual ℝ E := jnBlockApply b z
  have hy : ∀ n, ‖y n‖ ≤ R := jn_block_preserves_bound hzbound b
  have hlower : ∀ k, δ ≤ ‖jnRademacherFunctional L y R hy k‖ := by
    intro k
    let x := (jnStableStageData hz k).x
    have hvalue : δ ≤ jnRademacherFunctional L y R hy k x := by
      rw [jn_rademacherFunctional_apply]
      apply jn_banach_of_positive_block_means L hpos hone hshift
        (2 ^ (k + 1)) (by positivity)
      intro n hn
      calc
        δ ≤ jnBlockApply (jnRademacherBlocking k) y n x := by
          simpa only [y, b, x] using jn_stableDiagonal_good hz k n hn
        _ = ((2 ^ (k + 1) : ℕ) : ℝ)⁻¹ *
            ∑ i ∈ Finset.range (2 ^ (k + 1)),
              (jnRademacher k * jnBoundedEval y R hy x)
                (2 ^ (k + 1) * n + i) :=
          (jn_rademacher_block_mean_eval y R hy k n x).symm
    calc
      δ ≤ jnRademacherFunctional L y R hy k x := hvalue
      _ ≤ ‖jnRademacherFunctional L y R hy k x‖ := Real.le_norm_self _
      _ ≤ ‖jnRademacherFunctional L y R hy k‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖jnRademacherFunctional L y R hy k‖ * 1 :=
        mul_le_mul_of_nonneg_left (jnStableStageData hz k).norm_le (norm_nonneg _)
      _ = ‖jnRademacherFunctional L y R hy k‖ := mul_one _
  exact jn_of_rademacher_lower_bound L hpos hone hshift y R hy δ hδ hlower

theorem jn_stable_block_or_pointwise_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℕ → StrongDual ℝ E) :
    (∃ b : JnBlocking, JnPointwiseNull (jnBlockApply b z)) ∨
      ∃ (b : JnBlocking) (δ : ℝ), 0 < δ ∧
        JnBlockStable δ (jnBlockApply b z) := by
  classical
  by_cases hs : ∃ (b : JnBlocking) (δ : ℝ), 0 < δ ∧
      JnBlockStable δ (jnBlockApply b z)
  · exact Or.inr hs
  · left
    push Not at hs
    have hsmall : ∀ (base : JnBlocking) (q : ℕ),
        ∃ next : JnBlocking, ∀ x : E, ‖x‖ ≤ 1 →
          ∃ N, ∀ n, N ≤ n →
            ‖jnBlockApply next (jnBlockApply base z) n x‖ <
              1 / ((q : ℝ) + 1) := by
      intro base q
      exact jn_not_stable_small (hs base (1 / ((q : ℝ) + 1)) (by positivity))
    let next (base : JnBlocking) (q : ℕ) : JnBlocking :=
      Classical.choose (hsmall base q)
    let states : ℕ → JnBlocking := fun n =>
      Nat.rec jnIdBlocking (fun q base => jnBlockingComp base (next base q)) n
    let step : ℕ → JnBlocking := fun q => next (states q) q
    have hstates_zero : states 0 = jnIdBlocking := rfl
    have hstates_succ : ∀ q, states (q + 1) =
        jnBlockingComp (states q) (step q) := fun q => rfl
    have hstates_chain : ∀ q, states q = jnBlockingChain step q := by
      intro q
      induction q with
      | zero => rfl
      | succ q ih =>
          rw [show q + 1 = q.succ from rfl, hstates_succ q, jnBlockingChain, ih]
    let diagonal := jnDiagonalBlocking step
    refine ⟨diagonal, ?_⟩
    intro x
    by_cases hx : x = 0
    · subst x
      simpa only [map_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
          Filter.atTop (nhds 0))
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let y : E := ‖x‖⁻¹ • x
      have hy : ‖y‖ ≤ 1 := by
        have hy_eq : ‖y‖ = 1 := by
          simp [y, norm_smul, inv_mul_cancel₀ (ne_of_gt hxpos)]
        exact hy_eq.le
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨q, hq⟩ := exists_nat_one_div_lt (div_pos hε hxpos)
      have hnext := Classical.choose_spec (hsmall (states q) q) y hy
      obtain ⟨N, hN⟩ := hnext
      have hN' : ∀ i, N ≤ i →
          ‖jnBlockApply (states (q + 1)) z i y‖ < 1 / ((q : ℝ) + 1) := by
        intro i hi
        rw [hstates_succ, jn_blockApply_comp]
        exact hN i hi
      let M := max (q + 1) N
      refine ⟨M, fun n hn => ?_⟩
      have hqn : q + 1 ≤ n := (le_max_left _ _).trans hn
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hqn
      have hdiag := jn_blockApply_diagonal step z (q + 1) d
      rw [← hstates_chain (q + 1)] at hdiag
      have hsmall_diag : ‖jnBlockApply diagonal z n y‖ < 1 / ((q : ℝ) + 1) := by
        rw [hd]
        rw [hdiag]
        apply jn_blockApply_eval_lt
        intro i hi
        apply hN' i
        apply ((le_max_right _ _).trans hn).trans
        simpa only [hd] using
          (jn_block_index_le_support (jnBlockingTailChain step (q + 1) d)
            (q + 1 + d) i hi)
      rw [dist_zero_right]
      have hxy : x = ‖x‖ • y := by
        symm
        simp [y, smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos)]
      have hfinal : ‖x‖ * ‖jnBlockApply diagonal z n y‖ < ε := by
        calc
        ‖x‖ * ‖jnBlockApply diagonal z n y‖ <
            ‖x‖ * (1 / ((q : ℝ) + 1)) :=
          mul_lt_mul_of_pos_left hsmall_diag hxpos
        _ < ε := by
          have := mul_lt_mul_of_pos_left hq hxpos
          calc
            ‖x‖ * (1 / ((q : ℝ) + 1)) < ‖x‖ * (ε / ‖x‖) := this
            _ = ε := by
              rw [div_eq_mul_inv]
              calc
                ‖x‖ * (ε * ‖x‖⁻¹) = ε * (‖x‖ * ‖x‖⁻¹) := by ring
                _ = ε := by rw [mul_inv_cancel₀ hxpos.ne', mul_one]
      calc
        ‖‖jnBlockApply diagonal z n x‖‖ = ‖jnBlockApply diagonal z n x‖ := norm_norm _
        _ = ‖x‖ * ‖jnBlockApply diagonal z n y‖ := by
          have happ : jnBlockApply diagonal z n x =
              ‖x‖ • jnBlockApply diagonal z n y := by
            calc
              jnBlockApply diagonal z n x =
                  jnBlockApply diagonal z n (‖x‖ • y) :=
                congrArg (fun v : E => (jnBlockApply diagonal z n) v) hxy
              _ = ‖x‖ • jnBlockApply diagonal z n y :=
                (jnBlockApply diagonal z n).map_smul ‖x‖ y
          rw [happ, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg x)]
        _ < ε := hfinal

theorem jn_l1Lower_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) :
    LinearIndependent ℝ x := by
  rw [linearIndependent_iff]
  intro a ha
  have h := hx a
  rw [ha, norm_zero] at h
  have hsum_nonneg : 0 ≤ a.sum (fun _ t => |t|) := by
    apply Finsupp.sum_nonneg
    exact fun _ _ => abs_nonneg _
  have hsum : a.sum (fun _ t => |t|) = 0 := by nlinarith
  apply Finsupp.ext
  intro i
  by_cases hi : i ∈ a.support
  · have hall : ∀ j ∈ a.support, |a j| = 0 := by
      rw [← Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)]
      exact hsum
    exact abs_eq_zero.mp (hall i hi)
  · change a i = 0
    simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using hi

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
