import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Lemma.Fin.Pi_ToMeasure.of.EqSum
import Lemma.Real.Any_And_AbsSub.le.DivCard.of.EqSum_1.All_Ge_0.Gt_0
import Lemma.Real.NhdsNegSum_Mul_LogDiv.of.All_Gt_0.All_LeAbsSub_DivCard.All_EqSum.All_Ge_0
import Initialize.Tactic.Attr.Basic
open ENNReal Filter Fin Finset MeasureTheory Real


private lemma liminf_open [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {ν : α → ℝ} {μ : PMF α} {U : Set (α → ℝ)} (hν : ∀ a, 0 ≤ ν a) (hsum : ∑ a, ν a = 1) (hμ : ∀ a, 0 < (μ a).toReal) (hU : IsOpen U) (hmem : ν ∈ U) :
  -toEReal (∑ a, ν a * log (ν a / (μ a).toReal)) ≤ liminf (fun n : ℕ => toEReal ((n : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U}).toReal))) atTop := by
  have hex : ∀ n, 0 < n → ∃ c : α → ℕ, ∑ a, c a = n ∧ ∀ a, |(c a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n :=
    fun n hn => Any_And_AbsSub.le.DivCard.of.EqSum_1.All_Ge_0.Gt_0 hn hν hsum
  let c : ℕ → α → ℕ := fun n => if hn : 0 < n then Classical.choose (hex n hn) else 0
  have hspec : ∀ n, 0 < n → ∑ a, c n a = n ∧ ∀ a, |(c n a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n := by
    intro n hn
    simpa [c, hn] using Classical.choose_spec (hex n hn)
  let m : α → ℝ := fun a => (μ a).toReal
  have hrate :=
    NhdsNegSum_Mul_LogDiv.of.All_Gt_0.All_LeAbsSub_DivCard.All_EqSum.All_Ge_0 hν (fun n hn => (hspec n hn).1) (fun n hn => (hspec n hn).2) hμ
  have hcoord : ∀ a, Tendsto (fun n => (c n a : ℝ) / n) atTop (nhds (ν a)) := by
    intro a
    have habs : Tendsto (fun n => |(c n a : ℝ) / n - ν a|) atTop (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ (tendsto_const_div_atTop_nhds_zero_nat (Fintype.card α : ℝ))
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (hspec n hn).2 a
    simpa [Metric.tendsto_atTop, dist_eq, abs_abs] using habs
  have hfreq : Tendsto (fun n => fun a => (c n a : ℝ) / n) atTop (nhds ν) := by
    rwa [tendsto_pi_nhds]
  have hUev : ∀ᶠ n in atTop, (fun a => (c n a : ℝ) / n) ∈ U := hfreq (hU.mem_nhds hmem)
  let g : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * log ((Nat.multinomial univ (c n) : ℝ) * ∏ a, m a ^ c n a)
  let f : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U}).toReal)
  have hge : ∀ᶠ n in atTop, g n ≤ f n := by
    filter_upwards [eventually_gt_atTop 0, hUev] with n hn hUn
    have hsumc : ∑ a, c n a = n := (hspec n hn).1
    have hsub : {ω : Fin n → α | ∀ a, countVec ω a = c n a} ⊆ {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U} := by
      intro ω hω
      simpa [show ∀ a, countVec ω a = c n a from hω] using hUn
    have hleμ := measure_mono (μ := Measure.pi fun _ : Fin n => μ.toMeasure) hsub
    have heq := Pi_ToMeasure.of.EqSum hsumc μ
    have hto : ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | ∀ a, countVec ω a = c n a}).toReal = (Nat.multinomial univ (c n) : ℝ) * ∏ a, m a ^ c n a := by
      rw [heq]
      simp only [toReal_mul, toReal_natCast, toReal_prod, toReal_pow, m]
    have hmass : 0 < (Nat.multinomial univ (c n) : ℝ) * ∏ a, m a ^ c n a := by
      refine mul_pos (by exact_mod_cast Nat.multinomial_pos univ (c n)) ?_
      refine prod_pos fun a _ => pow_pos (hμ a) _
    have htop : (Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U} ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ _))
      rw [Measure.pi_univ]
      simp
    have hreal : (Nat.multinomial univ (c n) : ℝ) * ∏ a, m a ^ c n a ≤ ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U}).toReal := by
      rw [← hto]
      exact toReal_mono htop hleμ
    have hlog := log_le_log hmass hreal
    simpa [g, f] using mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hlimg : liminf (fun n => toEReal (g n)) atTop = -toEReal (∑ a, ν a * log (ν a / (μ a).toReal)) := by
    rw [← EReal.coe_neg]
    apply Tendsto.liminf_eq
    simpa [g, m] using EReal.tendsto_coe.mpr hrate
  rw [← hlimg]
  rw [liminf_eq, liminf_eq]
  refine sSup_le_sSup ?_
  intro a ha
  filter_upwards [ha, hge] with n hn hle
  exact hn.trans (EReal.coe_le_coe_iff.mpr hle)

/--
If an open set of real vectors contains a probability vector `ν`, the logarithmic probability
that the empirical frequency lands in that set has liminf at least `-KL(ν ‖ μ)`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {ν : α → ℝ} {μ : PMF α} {U : Set (α → ℝ)}
-- given
  (hν : ∀ a, 0 ≤ ν a)
  (hsum : ∑ a, ν a = 1)
  (hμ : ∀ a, 0 < (μ a).toReal)
  (hU : IsOpen U)
  (hmem : ν ∈ U) :
-- imply
  -toEReal (∑ a, ν a * log (ν a / (μ a).toReal)) ≤
    liminf (fun n : ℕ => toEReal ((n : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U}).toReal))) atTop :=
-- proof
  liminf_open hν hsum hμ hU hmem


-- created on 2026-11-02
