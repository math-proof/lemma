import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Lemma.Real.AbsAddMulInvLogSum_MulDivLog.le.DivMulCardAddDivLog2'1.of.All_Gt_0.EqSum.Gt_0
import Lemma.Real.Nhds_Sum_Mul_LogDiv.of.All_Gt_0.All_LeAbsSub_DivCard.All_Ge_0
import Initialize.Tactic.Attr.Basic
open Asymptotics Filter Finset Real


private lemma tendsto_err [Fintype α] : Tendsto (fun n : ℕ => (Fintype.card α : ℝ) * (log (n : ℝ) / 2 + 1) / n) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ) / n) atTop (nhds 0) :=
    isLittleO_log_id_atTop.natCast_atTop.tendsto_div_nhds_zero
  have hinner : Tendsto (fun n : ℕ => 2⁻¹ * (log (n : ℝ) / n) + (n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa using (hlog.const_mul 2⁻¹).add tendsto_one_div_atTop_nhds_zero_nat
  refine Tendsto.congr (fun n => ?_) (by simpa using hinner.const_mul (Fintype.card α : ℝ))
  ring

private lemma tendsto_rate [Fintype α] [DecidableEq α] {c : ℕ → α → ℕ} {ν m : α → ℝ} (hν : ∀ a, 0 ≤ ν a) (hsum : ∀ n, 0 < n → ∑ a, c n a = n) (hclose : ∀ n, 0 < n → ∀ a, |(c n a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n) (hm : ∀ a, 0 < m a) :
  Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * log ((Nat.multinomial univ (c n) : ℝ) * ∏ a, m a ^ c n a)) atTop (nhds (-∑ a, ν a * log (ν a / m a))) := by
  let rate : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * log ((Nat.multinomial univ (c n) : ℝ) * ∏ a, m a ^ c n a)
  let kl : ℕ → ℝ := fun n => ∑ a, ((c n a : ℝ) / n) * log (((c n a : ℝ) / n) / m a)
  have hgap : Tendsto (fun n => rate n + kl n) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
      (show Tendsto (fun n : ℕ => (Fintype.card α : ℝ) * (log (n : ℝ) / 2 + 1) / n) atTop (nhds 0) from tendsto_err)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hle :=
      AbsAddMulInvLogSum_MulDivLog.le.DivMulCardAddDivLog2'1.of.All_Gt_0.EqSum.Gt_0 hn (hsum n hn) (fun a _ => hm a)
    simpa [rate, kl] using hle
  have hkl : Tendsto kl atTop (nhds (∑ a, ν a * log (ν a / m a))) := by
    simpa [kl] using Nhds_Sum_Mul_LogDiv.of.All_Gt_0.All_LeAbsSub_DivCard.All_Ge_0 hν hclose hm
  have hsub : Tendsto (fun n => rate n + kl n - kl n) atTop (nhds (-∑ a, ν a * log (ν a / m a))) := by
    simpa [zero_sub] using hgap.sub hkl
  refine Tendsto.congr (fun n => ?_) hsub
  ring

/--
The logarithmic multinomial probability of an empirical type within `|α| / n` of a nonnegative
vector tends to the negative relative entropy of that vector.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  {c : ℕ → α → ℕ} {ν m : α → ℝ}
-- given
  (hν : ∀ a, 0 ≤ ν a)
  (hsum : ∀ n, 0 < n → ∑ a, c n a = n)
  (hclose : ∀ n, 0 < n → ∀ a, |(c n a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n)
  (hm : ∀ a, 0 < m a) :
-- imply
  Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * log ((Nat.multinomial univ (c n) : ℝ) * ∏ a, m a ^ c n a)) atTop
    (nhds (-∑ a, ν a * log (ν a / m a))) :=
-- proof
  tendsto_rate hν hsum hclose hm


-- created on 2026-11-02
