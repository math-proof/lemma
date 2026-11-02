import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Lemma.Finset.AbsAddMulInvLogInf'.le.DivMulCardAddAddLogDivLog2'1.of.All_GtToReal_0.Nonempty.All_EqSum.Gt_0
open Asymptotics Filter Finset MeasureTheory Real


private lemma tendsto_log_div : Tendsto (fun n : ℕ => log (n : ℝ) / n) atTop (nhds 0) :=
  isLittleO_log_id_atTop.natCast_atTop.tendsto_div_nhds_zero

private lemma tendsto_log_succ_div : Tendsto (fun n : ℕ => log ((n : ℝ) + 1) / n) atTop (nhds 0) := by
  have hquot : Tendsto (fun n : ℕ => log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (nhds 1) := by
    have hsum : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    refine Tendsto.congr' ?_ hsum
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp [Nat.cast_ne_zero.mpr hn]
  refine Tendsto.congr' ?_ (by simpa using hquot.mul hratio)
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp [Nat.cast_ne_zero.mpr hn]

private lemma tendsto_err [Fintype α] : Tendsto (fun n : ℕ => (Fintype.card α : ℝ) * (log ((n : ℝ) + 1) + log (n : ℝ) / 2 + 1) / n) atTop (nhds 0) := by
  have hexp :=
    (tendsto_log_succ_div.add ((tendsto_log_div.const_mul (1 / 2)).add tendsto_one_div_atTop_nhds_zero_nat)).const_mul
      (Fintype.card α : ℝ)
  refine Tendsto.congr' ?_ (by simpa using hexp)
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp [Nat.cast_ne_zero.mpr hn]
  ring

private lemma tendsto_rate [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {s : ℕ → Finset (α → ℕ)} {μ : PMF α} (hs : ∀ n, 0 < n → ∀ c ∈ s n, ∑ a, c a = n) (hne : ∀ n, 0 < n → (s n).Nonempty) (hμ : ∀ n, 0 < n → ∀ c ∈ s n, ∀ a, 0 < c a → 0 < (μ a).toReal) :
  Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin (n + 1) => μ.toMeasure) (⋃ c ∈ s (n + 1), (empiricalSet (n + 1) c : Set (Fin (n + 1) → α)))).toReal) + (s (n + 1)).inf' (hne (n + 1) n.succ_pos) (fun c => ∑ a, ((c a : ℝ) / (n + 1)) * log (((c a : ℝ) / (n + 1)) / (μ a).toReal))) atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun _ => abs_nonneg _)
  ·
    intro n
    simpa using
      AbsAddMulInvLogInf'.le.DivMulCardAddAddLogDivLog2'1.of.All_GtToReal_0.Nonempty.All_EqSum.Gt_0
        n.succ_pos (hs (n + 1) n.succ_pos) (hne (n + 1) n.succ_pos) (hμ (n + 1) n.succ_pos)
  ·
    simpa [Nat.cast_add] using (tendsto_add_atTop_iff_nat 1).mpr tendsto_err

/--
Along i.i.d. samples from a finite alphabet, `(1/n) log` of the probability of a nonempty union of
empirical types and the infimum relative entropy of those types sum to `0` in the limit.
The Stirling and type-counting error is `|α| (log (n + 1) + log n / 2 + 1) / n`, which is `o(1)`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {s : ℕ → Finset (α → ℕ)} {μ : PMF α}
-- given
  (hs : ∀ n, 0 < n → ∀ c ∈ s n, ∑ a, c a = n)
  (hne : ∀ n, 0 < n → (s n).Nonempty)
  (hμ : ∀ n, 0 < n → ∀ c ∈ s n, ∀ a, 0 < c a → 0 < (μ a).toReal) :
-- imply
  Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin (n + 1) => μ.toMeasure) (⋃ c ∈ s (n + 1), (empiricalSet (n + 1) c : Set (Fin (n + 1) → α)))).toReal) + (s (n + 1)).inf' (hne (n + 1) n.succ_pos) (fun c => ∑ a, ((c a : ℝ) / (n + 1)) * log (((c a : ℝ) / (n + 1)) / (μ a).toReal))) atTop (nhds 0) :=
-- proof
  tendsto_rate hs hne hμ


-- created on 2026-11-02
