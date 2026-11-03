import Lemma.Random.Any_And_Any_All_LeAbsAndLe_Integral_Sub_Log_Integral_Exp.of.EqKlDiv_Top
import Lemma.Random.Any_ContinuousAndAny_All_LeAbsAndLeSubToRealIntegral_Sub_Log.of.Lt0
import Lemma.Random.IsProbabilityMeasure.of.Gt_0
import Lemma.Random.Limsup_MulInvERealLog.le.AddNegLog_Integral_Exp.of.All_Le_Integral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.LiminfLimsup
import Initialize.Tactic.Attr.Basic
open BoundedContinuousFunction Classical ENNReal Filter Finset InformationTheory MeasureTheory ProbabilityMeasure Random Real Set
open scoped ENNReal Topology


universe u


private lemma leNeg {a b : EReal} (h : ∀ t : ℝ, ↑t < b → a ≤ -↑t) : a ≤ -b := by
  cases b with
  | bot =>
    exact le_top.trans_eq EReal.neg_bot.symm
  | top =>
    cases a with
    | bot =>
      rw [EReal.neg_top]
    | coe q =>
      exfalso
      have hq : ((-q + 1 : ℝ) : EReal) < ⊤ := EReal.coe_lt_top (-q + 1)
      have hle := h (-q + 1) hq
      rw [← EReal.coe_neg, EReal.coe_le_coe_iff] at hle
      linarith
    | top =>
      exfalso
      have hle := h 0 (EReal.coe_lt_top 0)
      rw [← EReal.coe_neg] at hle
      exact not_le_of_gt (EReal.coe_lt_top _) hle
  | coe r =>
    cases a with
    | bot => exact bot_le
    | top =>
      exfalso
      have hle := h (r - 1) (EReal.coe_lt_coe_iff.mpr (by linarith))
      rw [← EReal.coe_neg] at hle
      exact not_le_of_gt (EReal.coe_lt_top _) hle
    | coe q =>
      rw [← EReal.coe_neg, EReal.coe_le_coe_iff]
      by_contra hqr
      push Not at hqr
      have hlt : -q < r := by linarith
      obtain ⟨t, ht1, ht2⟩ := exists_between hlt
      have hle := h t (EReal.coe_lt_coe_iff.mpr ht2)
      rw [← EReal.coe_neg, EReal.coe_le_coe_iff] at hle
      linarith

private lemma openRate
  {α : Type u} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {K : Set (ProbabilityMeasure α)} {ν : ProbabilityMeasure α} {t : ℝ}
-- given
  (ht : ↑t < (klDiv (ν : Measure α) μ : EReal)) :
-- imply
  ∃ U : Set (ProbabilityMeasure α), IsOpen U ∧ ν ∈ U ∧
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
      ((@Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
        (fun ω => if hn : 0 < n then
          (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
            IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
        else μ.toProbabilityMeasure)
        (Measure.pi fun _ : Fin n => μ)) (U ∩ K))) atTop ≤ -↑t :=
-- proof
by
  let law (n : ℕ) : Measure (ProbabilityMeasure α) :=
    @Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
      (fun ω => if hn : 0 < n then
        (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
          IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
      else μ.toProbabilityMeasure)
      (Measure.pi fun _ : Fin n => μ)
  show ∃ U : Set (ProbabilityMeasure α), IsOpen U ∧ ν ∈ U ∧
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n (U ∩ K))) atTop ≤ -↑t
  have htest : ∃ g : α → ℝ, Continuous g ∧ (∃ C, ∀ x, |g x| ≤ C) ∧
      t < ∫ x, g x ∂(ν : Measure α) - log (∫ x, exp (g x) ∂μ) := by
    if htop : klDiv (ν : Measure α) μ = ⊤ then
      obtain ⟨g, hg, hC, hge⟩ :=
        Any_And_Any_All_LeAbsAndLe_Integral_Sub_Log_Integral_Exp.of.EqKlDiv_Top htop (t + 1)
      exact ⟨g, hg, hC, lt_of_lt_of_le (by linarith) hge⟩
    else
      have hpair := (klDiv_ne_top_iff (μ := ν) (ν := μ)).mp htop
      have hcoe : (klDiv (ν : Measure α) μ : EReal) =
          ↑((klDiv (ν : Measure α) μ).toReal) :=
        (EReal.coe_ennreal_toReal htop).symm
      rw [hcoe] at ht
      have ht' : t < (klDiv (ν : Measure α) μ).toReal := EReal.coe_lt_coe_iff.mp ht
      have hε : 0 < ((klDiv (ν : Measure α) μ).toReal - t) / 2 := by linarith
      obtain ⟨g, hg, hC, hge⟩ :=
        Any_ContinuousAndAny_All_LeAbsAndLeSubToRealIntegral_Sub_Log.of.Lt0 hpair.1 hpair.2 hε
      refine ⟨g, hg, hC, ?_⟩
      have : (klDiv (ν : Measure α) μ).toReal - ((klDiv (ν : Measure α) μ).toReal - t) / 2 =
          ((klDiv (ν : Measure α) μ).toReal + t) / 2 := by ring
      linarith
  obtain ⟨g, hg, ⟨C, hC⟩, hgt⟩ := htest
  let φ := ofNormedAddCommGroup g hg C fun x => by simpa [Real.norm_eq_abs] using hC x
  have hcoeφ : (φ : α → ℝ) = g := coe_ofNormedAddCommGroup g hg C _
  have hexpr : t < ∫ x, φ x ∂(ν : Measure α) - log (∫ x, exp (φ x) ∂μ) := by
    simpa [hcoeφ] using hgt
  let δ : ℝ := (∫ x, φ x ∂(ν : Measure α) - log (∫ x, exp (φ x) ∂μ)) - t
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let c : ℝ := ∫ x, φ x ∂(ν : Measure α) - δ
  have hc : -c + log (∫ x, exp (φ x) ∂μ) ≤ -t := by
    dsimp [c, δ]
    linarith
  let U : Set (ProbabilityMeasure α) := {ρ | c < ∫ x, φ x ∂(ρ : Measure α)}
  have hUo : IsOpen U :=
    isOpen_lt continuous_const (continuous_integral_boundedContinuousFunction φ)
  have hνU : ν ∈ U := by
    simp [U, c]
    linarith
  refine ⟨U, hUo, hνU, ?_⟩
  have hmem : ∀ ρ ∈ U ∩ K, c ≤ ∫ x, φ x ∂(ρ : Measure α) := by
    intro ρ hρ
    exact le_of_lt hρ.1
  refine (Limsup_MulInvERealLog.le.AddNegLog_Integral_Exp.of.All_Le_Integral (μ := μ) (f := φ)
    (c := c) hmem).trans (EReal.coe_le_coe_iff.mpr hc)

/--
On a Polish space, the empirical measures of i.i.d. samples obey the compact-set upper bound in
Sanov's theorem. The speed is the sample size and the rate is the Kullback–Leibler divergence
from the common law.
-/
@[path]
private lemma main
  {α : Type u} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {K : Set (ProbabilityMeasure α)}
-- given
  (hK : IsCompact K) :
-- imply
  limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
    ((@Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
        (fun ω => if hn : 0 < n then
          (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
            IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
        else μ.toProbabilityMeasure)
        (Measure.pi fun _ : Fin n => μ)) K)) atTop ≤
    -(⨅ ν ∈ K, (klDiv (ν : Measure α) μ : EReal)) :=
-- proof
by
  let law (n : ℕ) : Measure (ProbabilityMeasure α) :=
    @Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
      (fun ω => if hn : 0 < n then
        (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
          IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
      else μ.toProbabilityMeasure)
      (Measure.pi fun _ : Fin n => μ)
  show limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K)) atTop ≤
    -(⨅ ν ∈ K, (klDiv (ν : Measure α) μ : EReal))
  let β : EReal := ⨅ ν ∈ K, (klDiv (ν : Measure α) μ : EReal)
  change limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K)) atTop ≤ -β
  apply leNeg
  intro t ht
  let ι := Subtype (fun ν : ProbabilityMeasure α => ν ∈ K)
  have hpack : ∀ i : ι, ∃ U : Set (ProbabilityMeasure α), IsOpen U ∧ i.1 ∈ U ∧
      limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n (U ∩ K))) atTop ≤ -↑t := by
    intro i
    exact openRate (lt_of_lt_of_le ht (iInf₂_le i.1 i.2))
  choose U hUo hUmem hUlim using hpack
  have hcover : K ⊆ ⋃ i : ι, U i := by
    intro ν hν
    exact mem_iUnion.mpr ⟨⟨ν, hν⟩, hUmem _⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hUo hcover
  if hcard : s.card = 0 then
    have hsempty : s = ∅ := Finset.card_eq_zero.mp hcard
    have hKe : K ⊆ (∅ : Set (ProbabilityMeasure α)) := by simpa [hsempty] using hs
    have hKempty : K = ∅ := subset_empty_iff.mp hKe
    have h0 : ∀ n, law n K = 0 := by
      intro n
      simp [hKempty, measure_empty]
    have hterm : ∀ᶠ n in atTop, ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K) = ⊥ := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [h0 n, ENNReal.log_zero, ← EReal.coe_coe_eq_natCast, ← EReal.coe_inv (n : ℝ)]
      exact EReal.coe_mul_bot_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hn))
    have hlim : limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K)) atTop = ⊥ := by
      rw [Filter.limsup_congr hterm, Filter.limsup_const]
    rw [hlim]
    exact bot_le
  else
    have hpos : 0 < s.card := Nat.pos_of_ne_zero hcard
    have hsub : K ⊆ ⋃ i ∈ s, U i ∩ K := by
      intro ν hν
      have hνU := hs hν
      simp only [mem_iUnion] at hνU
      obtain ⟨i, hi, hνi⟩ := hνU
      exact mem_iUnion₂.mpr ⟨i, hi, hνi, hν⟩
    have hsum : ∀ n, law n K ≤ ∑ i ∈ s, law n (U i ∩ K) := by
      intro n
      exact (measure_mono hsub).trans (measure_biUnion_finset_le s fun i => U i ∩ K)
    have hcard : ∀ n, ∑ i ∈ s, law n (U i ∩ K) ≤
        s.card • ⨆ i ∈ s, law n (U i ∩ K) := by
      intro n
      refine Finset.sum_le_card_nsmul s (fun i => law n (U i ∩ K))
        (⨆ i ∈ s, law n (U i ∩ K)) ?_
      intro i hi
      exact le_iSup₂ (f := fun i (_ : i ∈ s) => law n (U i ∩ K)) i hi
    have hsne : s.Nonempty := Finset.card_pos.mp hpos
    have hnn : ∀ n : ℕ, 0 ≤ ((n : ℕ) : EReal) := fun n => by exact_mod_cast Nat.zero_le n
    have hterm : ∀ n, 0 < n →
        ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K) ≤
          ((n : ℕ) : EReal)⁻¹ * ENNReal.log (s.card : ℝ≥0∞) +
            s.sup' hsne (fun i => ((n : ℕ) : EReal)⁻¹ *
              ENNReal.log (law n (U i ∩ K))) := by
      intro n hn
      have hleμ : law n K ≤ (s.card : ℝ≥0∞) * ⨆ i ∈ s, law n (U i ∩ K) := by
        calc
          law n K ≤ ∑ i ∈ s, law n (U i ∩ K) := hsum n
          _ ≤ s.card • ⨆ i ∈ s, law n (U i ∩ K) := hcard n
          _ = (s.card : ℝ≥0∞) * ⨆ i ∈ s, law n (U i ∩ K) := nsmul_eq_mul _ _
      have hlogsup : ENNReal.log (⨆ i ∈ s, law n (U i ∩ K)) =
          s.sup' hsne (fun i => ENNReal.log (law n (U i ∩ K))) := by
        rw [← Finset.sup_eq_iSup, Finset.sup'_eq_sup hsne]
        exact Finset.apply_sup_eq_sup_comp_of_nonempty ENNReal.log_monotone hsne
      have hscale : ((n : ℕ) : EReal)⁻¹ *
          s.sup' hsne (fun i => ENNReal.log (law n (U i ∩ K))) =
          s.sup' hsne (fun i => ((n : ℕ) : EReal)⁻¹ *
            ENNReal.log (law n (U i ∩ K))) := by
        rw [Finset.sup'_eq_sup hsne, Finset.sup'_eq_sup hsne]
        exact Finset.apply_sup_eq_sup_comp_of_nonempty
          (monotone_mul_left_of_nonneg (EReal.inv_nonneg_of_nonneg (hnn n))) hsne
      refine (mul_le_mul_of_nonneg_left (ENNReal.log_le_log hleμ)
        (EReal.inv_nonneg_of_nonneg (hnn n))).trans ?_
      rw [ENNReal.log_mul_add, EReal.left_distrib_of_nonneg_of_ne_top
        (EReal.inv_nonneg_of_nonneg (hnn n)) (EReal.inv_lt_top _).ne, hlogsup, hscale]
    have hle_fun : ∀ᶠ n in atTop,
        ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K) ≤
          ((n : ℕ) : EReal)⁻¹ * ENNReal.log (s.card : ℝ≥0∞) +
            s.sup' hsne (fun i => ((n : ℕ) : EReal)⁻¹ *
              ENNReal.log (law n (U i ∩ K))) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact hterm n hn
    have hcard0 : Tendsto (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (s.card : ℝ≥0∞))
        atTop (𝓝 0) := by
      have hlogc : ENNReal.log (s.card : ℝ≥0∞) = (Real.log (s.card : ℝ) : EReal) := by
        rw [ENNReal.log_pos_real (Nat.cast_ne_zero.mpr hpos.ne') (ENNReal.natCast_ne_top _),
          ENNReal.toReal_natCast]
      rw [hlogc]
      have hreal : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (s.card : ℝ)) atTop (𝓝 0) := by
        have hmul :=
          (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
            (Real.log (s.card : ℝ))
        simpa [zero_mul] using hmul
      have hfun : ∀ᶠ n in atTop,
          ((n : ℕ) : EReal)⁻¹ * (Real.log (s.card : ℝ) : EReal) =
            ((n : ℝ)⁻¹ * Real.log (s.card : ℝ) : EReal) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [← EReal.coe_coe_eq_natCast n, ← EReal.coe_inv (n : ℝ), ← EReal.coe_mul]
      refine (tendsto_congr' hfun).mpr (EReal.tendsto_coe.mpr hreal)
    have hlimS : limsup (fun n => s.sup' hsne (fun i => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (law n (U i ∩ K)))) atTop ≤ -↑t := by
      rw [limsup_finset_sup' hsne]
      exact Finset.sup'_le hsne _ (fun i _ => hUlim i)
    refine (limsup_le_limsup hle_fun).trans ?_
    refine (EReal.limsup_add_le ?_ ?_).trans ?_
    · exact Or.inl (by rw [hcard0.limsup_eq]; exact EReal.zero_ne_bot)
    · exact Or.inl (by rw [hcard0.limsup_eq]; exact EReal.zero_ne_top)
    · rw [hcard0.limsup_eq, zero_add]
      exact hlimS


-- created on 2026-11-02
