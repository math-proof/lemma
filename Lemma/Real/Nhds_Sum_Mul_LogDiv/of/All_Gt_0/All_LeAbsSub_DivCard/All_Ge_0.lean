import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Initialize.Tactic.Attr.Basic
open Filter Finset Real


private lemma continuousOn_entropy {m : ℝ} (hm : 0 < m) : ContinuousOn (fun t : ℝ => t * log (t / m)) (Set.Ici 0) := by
  refine ContinuousOn.congr (f := fun t => t * log t - t * log m) ?_ ?_
  · apply (continuous_mul_log.sub (continuous_id.mul continuous_const)).continuousOn
  ·
    intro t ht
    change t * log (t / m) = t * log t - t * log m
    obtain rfl | ht0 := eq_or_lt_of_le (Set.mem_Ici.mp ht)
    · simp
    · rw [log_div ht0.ne' hm.ne', mul_sub]

private lemma tendsto_entropy_term {m ν : ℝ} {x : ℕ → ℝ} (hν : 0 ≤ ν) (hm : 0 < m) (hx : Tendsto x atTop (nhds ν)) (hx0 : ∀ n, 0 ≤ x n) :
  Tendsto (fun n => x n * log (x n / m)) atTop (nhds (ν * log (ν / m))) := by
  apply ((continuousOn_entropy hm).continuousWithinAt (Set.mem_Ici.mpr hν)).tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨hx, Eventually.of_forall fun n => Set.mem_Ici.mpr (hx0 n)⟩

private lemma tendsto_kl [Fintype α] {c : ℕ → α → ℕ} {ν m : α → ℝ} (hν : ∀ a, 0 ≤ ν a) (hclose : ∀ n, 0 < n → ∀ a, |(c n a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n) (hm : ∀ a, 0 < m a) :
  Tendsto (fun n : ℕ => ∑ a, ((c n a : ℝ) / n) * log (((c n a : ℝ) / n) / m a)) atTop (nhds (∑ a, ν a * log (ν a / m a))) := by
  apply tendsto_finsetSum (univ : Finset α)
  intro a _
  refine tendsto_entropy_term (hν a) (hm a) ?_ fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have habs : Tendsto (fun n : ℕ => |(c n a : ℝ) / n - ν a|) atTop (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ (tendsto_const_div_atTop_nhds_zero_nat (Fintype.card α : ℝ))
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hclose n hn a
  simpa [Metric.tendsto_atTop, dist_eq, abs_abs] using habs

/--
Relative entropy is continuous along empirical frequencies within `|α| / n` of a nonnegative
vector, as soon as every reference mass is positive.
-/
@[path]
private lemma main
  [Fintype α]
  {c : ℕ → α → ℕ} {ν m : α → ℝ}
-- given
  (hν : ∀ a, 0 ≤ ν a)
  (hclose : ∀ n, 0 < n → ∀ a, |(c n a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n)
  (hm : ∀ a, 0 < m a) :
-- imply
  Tendsto (fun n : ℕ => ∑ a, ((c n a : ℝ) / n) * log (((c n a : ℝ) / n) / m a)) atTop
    (nhds (∑ a, ν a * log (ν a / m a))) :=
-- proof
  tendsto_kl hν hclose hm


-- created on 2026-11-02
