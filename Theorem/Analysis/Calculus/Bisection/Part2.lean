/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Def.Analysis.Calculus.Bisection.Part2
/-!
This file constructs bisection sequences on real intervals and proves that their midpoints
converge to a bracketed root with the standard geometric error bound.
-/


namespace Real.Calculus.Bisection

theorem bisection_pairs_is_sequence (f : ℝ → ℝ) (a b : ℝ) :
    IsBisectionSequence f a b
      (fun n => (bisection_pairs f a b n).1)
      (fun n => (bisection_pairs f a b n).2) := by
  refine ⟨rfl, rfl, ?_⟩
  intro n
  dsimp only
  by_cases h : f (((bisection_pairs f a b n).1 + (bisection_pairs f a b n).2) / 2) ≤ 0
  · left
    exact ⟨h, by simp [bisection_pairs, h], by simp [bisection_pairs, h]⟩
  · right
    exact ⟨le_of_not_ge h, by simp [bisection_pairs, h], by simp [bisection_pairs, h]⟩

/-- A bisection sequence exists for every function and pair of endpoints. -/
theorem exists_isBisectionSequence (f : ℝ → ℝ) (a b : ℝ) :
    ∃ u v, IsBisectionSequence f a b u v :=
  ⟨fun n => (bisection_pairs f a b n).1,
    fun n => (bisection_pairs f a b n).2,
    bisection_pairs_is_sequence f a b⟩

theorem bisection_geometric_tendsto_zero (a b : ℝ) :
    Filter.Tendsto (fun n : ℕ => (b - a) / (2 : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hm := hp.const_mul (b - a)
  simpa [div_eq_mul_inv] using hm

theorem bisection_endpoint_limits
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (huv : IsBisectionSequence f a b u v) :
    ∃ c ∈ Set.Icc a b,
      Filter.Tendsto u Filter.atTop (nhds c) ∧
      Filter.Tendsto v Filter.atTop (nhds c) ∧
      ∀ n, u n ≤ c ∧ c ≤ v n := by
  have hinv := bisection_le_and_le hab huv
  have hnest := bisection_nesting hab huv
  have hmono : Monotone u := monotone_nat_of_le_succ fun n => (hnest n).1
  have hanti : Antitone v := antitone_nat_of_succ_le fun n => (hnest n).2.2
  have hbdd : BddAbove (Set.range u) := by
    refine ⟨b, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (hinv n).2.1.trans (hinv n).2.2
  let c := ⨆ n, u n
  have hu : Filter.Tendsto u Filter.atTop (nhds c) := by
    simpa only [c] using tendsto_atTop_ciSup hmono hbdd
  have hv_eq : ∀ n, v n = u n + (b - a) / (2 : ℝ) ^ n := by
    intro n
    linarith [bisection_interval_length huv n]
  have hv : Filter.Tendsto v Filter.atTop (nhds c) := by
    have hadd := hu.add (bisection_geometric_tendsto_zero a b)
    convert hadd using 1
    · ext n
      exact hv_eq n
    · simp
  have hac : a ≤ c := by
    simpa only [c, huv.1] using le_ciSup hbdd 0
  have hcb : c ≤ b := by
    simpa only [c] using ciSup_le (fun n => (hinv n).2.1.trans (hinv n).2.2)
  refine ⟨c, ⟨hac, hcb⟩, hu, hv, ?_⟩
  intro n
  constructor
  · simpa only [c] using le_ciSup hbdd n
  · apply le_of_tendsto hv
    exact Filter.eventually_atTop.2 ⟨n, fun k hnk => hanti hnk⟩

theorem bisection_limit_root
    {f : ℝ → ℝ} {a b c : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a ≤ 0) (hb : 0 ≤ f b) (huv : IsBisectionSequence f a b u v)
    (hc : c ∈ Set.Icc a b)
    (hu : Filter.Tendsto u Filter.atTop (nhds c))
    (hv : Filter.Tendsto v Filter.atTop (nhds c)) : f c = 0 := by
  have hinv := bisection_invariants hab ha hb huv
  have hu_mem : ∀ n, u n ∈ Set.Icc a b := fun n =>
    ⟨(hinv n).1, (hinv n).2.1.trans (hinv n).2.2.1⟩
  have hv_mem : ∀ n, v n ∈ Set.Icc a b := fun n =>
    ⟨(hinv n).1.trans (hinv n).2.1, (hinv n).2.2.1⟩
  have hu' : Filter.Tendsto u Filter.atTop (nhdsWithin c (Set.Icc a b)) :=
    tendsto_nhdsWithin_iff.2 ⟨hu, Filter.Eventually.of_forall hu_mem⟩
  have hv' : Filter.Tendsto v Filter.atTop (nhdsWithin c (Set.Icc a b)) :=
    tendsto_nhdsWithin_iff.2 ⟨hv, Filter.Eventually.of_forall hv_mem⟩
  have hfu : Filter.Tendsto (fun n => f (u n)) Filter.atTop (nhds (f c)) :=
    (hf c hc).tendsto.comp hu'
  have hfv : Filter.Tendsto (fun n => f (v n)) Filter.atTop (nhds (f c)) :=
    (hf c hc).tendsto.comp hv'
  have hfc_nonpos : f c ≤ 0 :=
    le_of_tendsto hfu (Filter.Eventually.of_forall fun n => (hinv n).2.2.2.1)
  have hfc_nonneg : 0 ≤ f c := by
    have hneg := hfv.neg
    have : -f c ≤ 0 := le_of_tendsto hneg <|
      Filter.Eventually.of_forall fun n => neg_nonpos.mpr (hinv n).2.2.2.2
    linarith
  exact le_antisymm hfc_nonpos hfc_nonneg

theorem bisection_midpoint_tendsto
    {c : ℝ} {u v : ℕ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds c))
    (hv : Filter.Tendsto v Filter.atTop (nhds c)) :
    Filter.Tendsto (fun n => (u n + v n) / 2) Filter.atTop (nhds c) := by
  simpa only [add_self_div_two] using (hu.add hv).div_const 2

theorem bisection_midpoint_error
    {f : ℝ → ℝ} {a b c : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v)
    (hc : ∀ n, u n ≤ c ∧ c ≤ v n) :
    ∀ n, |(u n + v n) / 2 - c| ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
  intro n
  calc
    |(u n + v n) / 2 - c| ≤ (v n - u n) / 2 := by
      rw [abs_le]
      constructor <;> linarith [(hc n).1, (hc n).2]
    _ = ((b - a) / (2 : ℝ) ^ n) / 2 := by rw [bisection_interval_length huv n]
    _ = (b - a) / (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      ring

/-- A sign bracket admits nested bisection intervals with exact geometric length. -/
theorem exists_isBisectionSequence_nested
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ u v : ℕ → ℝ, IsBisectionSequence f a b u v ∧
      (∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n) ∧
      (∀ n, v n - u n = (b - a) / (2 : ℝ) ^ n) ∧
      ∀ n, f (u n) * f (v n) ≤ 0 := by
  obtain ⟨u, v, hseq⟩ := exists_isBisectionSequence f a b
  refine ⟨u, v, hseq, hseq.nested hab, hseq.sub_eq, ?_⟩
  intro n
  have h := hseq.invariants hab ha hb n
  exact mul_nonpos_of_nonpos_of_nonneg h.2.2.2.1 h.2.2.2.2

/-- Bisection method: nested bracketing intervals halving in length at each
step while keeping a sign change. -/
theorem bisection_nested_intervals
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (_hf : ContinuousOn f (Set.Icc a b)) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ u v : ℕ → ℝ, IsBisectionSequence f a b u v ∧
      (∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n) ∧
      (∀ n, v n - u n = (b - a) / (2 : ℝ) ^ n) ∧
      ∀ n, f (u n) * f (v n) ≤ 0 := exists_isBisectionSequence_nested hab ha hb

/-- Bisection correctness with linear rate: the midpoints converge to a root
with error at most `(b - a) / 2 ^ (n + 1)`. -/
theorem bisection_approximate_root_with_rate
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a ≤ 0) (hb : 0 ≤ f b)
    (u v : ℕ → ℝ) (huv : IsBisectionSequence f a b u v) :
    ∃ c ∈ Set.Icc a b, f c = 0 ∧
      Filter.Tendsto (fun n => (u n + v n) / 2) Filter.atTop (nhds c) ∧
      ∀ n, |(u n + v n) / 2 - c| ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
  obtain ⟨c, hc, hu, hv, hbracket⟩ := bisection_endpoint_limits hab huv
  exact ⟨c, hc, bisection_limit_root hab hf ha hb huv hc hu hv,
    bisection_midpoint_tendsto hu hv, bisection_midpoint_error huv hbracket⟩

end Real.Calculus.Bisection
