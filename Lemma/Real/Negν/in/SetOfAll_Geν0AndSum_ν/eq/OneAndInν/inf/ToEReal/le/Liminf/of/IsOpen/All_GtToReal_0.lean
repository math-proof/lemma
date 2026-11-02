import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Lemma.Fin.Pi_ToMeasure.of.EqSum
import Lemma.Real.Any_And_AbsSub.le.DivCard.of.EqSum_1.All_Ge_0.Gt_0
import Lemma.Real.NegIn_SetOfAll_Ge_0AndSum.eq.OneAndIn.inf.ToEReal.le.Liminf.of.IsOpen.All_GtToReal_0
import Initialize.Tactic.Attr.Basic
open Filter Fin Finset MeasureTheory Real


private lemma liminf_ennreal [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {μ : PMF α} {U : Set (α → ℝ)} (hμ : ∀ a, 0 < (μ a).toReal) (hU : IsOpen U) :
  -(⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ U}, toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) ≤
    liminf (fun n : ℕ => ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U})) atTop := by
  classical
  let simplex := {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ U}
  let kl (ν : α → ℝ) : ℝ := ∑ a, ν a * log (ν a / (μ a).toReal)
  let realRate (n : ℕ) : EReal := toEReal ((n : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U}).toReal))
  let ennRate (n : ℕ) : EReal := ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U})
  obtain ⟨ν, hν⟩ | hempty := em (∃ ν, ν ∈ simplex)
  ·
    obtain ⟨hge, hsum, hmem⟩ := hν
    have hex : ∀ n, 0 < n → ∃ c : α → ℕ, ∑ a, c a = n ∧ ∀ a, |(c a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n :=
      fun n hn => Any_And_AbsSub.le.DivCard.of.EqSum_1.All_Ge_0.Gt_0 hn hge hsum
    let c : ℕ → α → ℕ := fun n => if hn : 0 < n then Classical.choose (hex n hn) else 0
    have hspec : ∀ n, 0 < n → ∑ a, c n a = n ∧ ∀ a, |(c n a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n := by
      intro n hn
      simpa [c, hn] using Classical.choose_spec (hex n hn)
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
    have hpos : ∀ᶠ n in atTop, 0 < (Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U} := by
      filter_upwards [eventually_gt_atTop 0, hUev] with n hn hUn
      have hsumc : ∑ a, c n a = n := (hspec n hn).1
      have hsub : {ω : Fin n → α | ∀ a, countVec ω a = c n a} ⊆ {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U} := by
        intro ω hω
        simpa [show ∀ a, countVec ω a = c n a from hω] using hUn
      have hmass : 0 < (Nat.multinomial univ (c n) : ENNReal) * ∏ a, μ a ^ c n a := by
        refine ENNReal.mul_pos ?_ ?_
        · exact_mod_cast (Nat.multinomial_pos univ (c n)).ne'
        ·
          refine prod_ne_zero_iff.mpr ?_
          intro a _
          exact pow_ne_zero _ ((ENNReal.toReal_pos_iff.mp (hμ a)).1).ne'
      refine lt_of_lt_of_le hmass ?_
      simpa [← Pi_ToMeasure.of.EqSum hsumc μ] using measure_mono hsub
    have heq : ∀ᶠ n in atTop, realRate n = ennRate n := by
      filter_upwards [eventually_gt_atTop 0, hpos] with n hn hP
      have htop : (Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U} ≠ ⊤ := by
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        refine le_trans (measure_mono (Set.subset_univ _)) ?_
        rw [Measure.pi_univ]
        simp
      have hlog := ENNReal.log_pos_real hP.ne' htop
      have hinv : ((n : EReal)⁻¹) = toEReal ((n : ℝ)⁻¹) := by
        rw [← EReal.coe_coe_eq_natCast n]
        exact (EReal.coe_inv (n : ℝ)).symm
      simp [realRate, ennRate, hlog, hinv, EReal.coe_mul]
    have hreal := NegIn_SetOfAll_Ge_0AndSum.eq.OneAndIn.inf.ToEReal.le.Liminf.of.IsOpen.All_GtToReal_0 hμ hU
    rw [← liminf_congr heq]
    simpa [realRate, kl, simplex] using hreal
  ·
    have htop : (⨅ ν ∈ simplex, toEReal (kl ν)) = ⊤ := by
      refine iInf_eq_top.mpr ?_
      intro ν
      let : IsEmpty (ν ∈ simplex) := ⟨fun h => hempty ⟨ν, h⟩⟩
      exact iInf_of_empty (f := fun _ => toEReal (kl ν))
    rw [htop, EReal.neg_top]
    apply bot_le

/--
If every reference mass is positive, the `ENNReal` logarithm of the probability that the empirical
frequency lands in an open set `U` has liminf at least the negative infimum of `KL(ν ‖ μ)` over
the probability vectors in `U`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : PMF α} {U : Set (α → ℝ)}
-- given
  (hμ : ∀ a, 0 < (μ a).toReal)
  (hU : IsOpen U) :
-- imply
  -(⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ U}, toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) ≤
    liminf (fun n : ℕ => ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U})) atTop :=
-- proof
  liminf_ennreal hμ hU


-- created on 2026-11-02
