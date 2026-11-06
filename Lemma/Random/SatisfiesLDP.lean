import Lemma.EReal.Le_Neg.of.All_Le_Neg
import Lemma.Random.IsProbabilityMeasure.of.Gt_0
import Lemma.Random.Limsup_MulInvERealLog.le.NegIn.inf.KlDivMeasure.of.IsCompact
import Lemma.Random.LowerSemicontinuous_KlDivMeasure
import Lemma.Random.Measurable.of.Gt_0
import Lemma.Random.NegIn.inf.KlDivMeasure.le.Liminf_MulInvERealLog.of.IsOpen
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Order.LiminfLimsup
open Classical ENNReal EReal Filter Finset InformationTheory MeasureTheory ProbabilityMeasure Random Set Real
open scoped ENNReal Topology
set_option maxHeartbeats 800000


private lemma tight
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
-- given
  (M : ℝ) :
-- imply
  ∃ Γ : Set (ProbabilityMeasure α), IsCompact Γ ∧
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
      ((@Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
        (fun ω => if hn : 0 < n then
          (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
            IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
        else μ.toProbabilityMeasure)
        (Measure.pi fun _ : Fin n => μ)) Γᶜ)) atTop ≤ -↑M := by
-- proof
  let emp (n : ℕ) (ω : Fin n → α) : ProbabilityMeasure α :=
    if hn : 0 < n then
      (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
        IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
    else
      μ.toProbabilityMeasure
  let law (n : ℕ) : Measure (ProbabilityMeasure α) :=
    @Measure.map (Fin n → α) (ProbabilityMeasure α) _ _ (emp n)
      (Measure.pi fun _ : Fin n => μ)
  have indicatorChernoff (A : Set α) (hA : MeasurableSet A) (t ε : ℝ) (ht : 0 < t) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ)
      {ω | ε * n ≤ ∑ i, A.indicator (fun _ => (1 : ℝ)) (ω i)} ≤
      ENNReal.ofReal (exp (-(t * ε) * n) *
        (∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ) ^ n) := by
    let g : α → ℝ := fun x => t * A.indicator (fun _ => (1 : ℝ)) x
    have hg : Measurable g := by
      simpa [g] using (measurable_const.indicator hA).const_mul t
    let c : ℝ := t * ε
    have hset : {ω : Fin n → α | ε * (n : ℝ) ≤ ∑ i, A.indicator (fun _ => (1 : ℝ)) (ω i)} =
      {ω : Fin n → α | c * n ≤ ∑ i, g (ω i)} := by
      ext ω
      simp only [mem_ofPred_eq, c, g, ← Finset.mul_sum]
      rw [mul_assoc]
      exact (mul_le_mul_iff_of_pos_left ht).symm
    rw [hset]
    let η : ℝ≥0∞ := ENNReal.ofReal (exp (c * n))
    let φ : (Fin n → α) → ℝ≥0∞ := fun ω => ENNReal.ofReal (exp (∑ i, g (ω i)))
    have hge : {ω | c * (n : ℝ) ≤ ∑ i, g (ω i)} = {ω | η ≤ φ ω} := by
      ext ω
      simp only [mem_ofPred_eq, η, φ]
      rw [ofReal_le_ofReal_iff (exp_pos _).le, exp_le_exp]
    rw [hge]
    have hη0 : η ≠ 0 := by simp [η, ofReal_eq_zero, not_le, exp_pos]
    have hηtop : η ≠ ∞ := ofReal_ne_top
    have hφ : AEMeasurable φ (Measure.pi fun _ : Fin n => μ) := by
      refine Measurable.aemeasurable ?_
      refine measurable_ofReal.comp ?_
      refine measurable_exp.comp ?_
      refine measurable_fun_sum Finset.univ fun i _ => ?_
      exact hg.comp (measurable_pi_apply i)
    have hmarkov := meas_ge_le_lintegral_div (μ := Measure.pi fun _ : Fin n => μ) hφ hη0 hηtop
    refine hmarkov.trans ?_
    have hint : Integrable (fun x => exp (g x)) μ := by
      refine ⟨(measurable_exp.comp hg).aestronglyMeasurable, ?_⟩
      refine HasFiniteIntegral.of_bounded (C := exp t) (ae_of_all _ fun x => ?_)
      show ‖exp (g x)‖ ≤ exp t
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      apply exp_le_exp.mpr
      simp only [g]
      have hind : A.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
        if hx : x ∈ A then
          simp [hx, indicator]
        else
          simp [hx, indicator]
      nlinarith [ht.le, hind]
    have hintn : Integrable (fun ω : Fin n → α => exp (∑ i, g (ω i)))
      (Measure.pi fun _ : Fin n => μ) := by
      have hrewrite : (fun ω : Fin n → α => exp (∑ i, g (ω i))) =
        fun ω => ∏ i, exp (g (ω i)) := by
        funext ω
        exact exp_sum Finset.univ fun i => g (ω i)
      rw [hrewrite]
      exact Integrable.fintype_prod fun _ => hint
    have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin n => μ] fun ω => exp (∑ i, g (ω i)) :=
      ae_of_all _ fun _ => (exp_pos _).le
    have hlin : ∫⁻ ω, φ ω ∂(Measure.pi fun _ : Fin n => μ) =
      ENNReal.ofReal (∫ ω, exp (∑ i, g (ω i)) ∂(Measure.pi fun _ : Fin n => μ)) := by
      simpa [φ] using (ofReal_integral_eq_lintegral_ofReal hintn hnn).symm
    rw [hlin]
    have hpow : ∫ ω, exp (∑ i, g (ω i)) ∂(Measure.pi fun _ : Fin n => μ) =
      (∫ x, exp (g x) ∂μ) ^ n := by
      have hrewrite : (fun ω : Fin n → α => exp (∑ i, g (ω i))) =
        fun ω => ∏ i, exp (g (ω i)) := by
        funext ω
        exact exp_sum Finset.univ fun i => g (ω i)
      rw [hrewrite]
      simpa [g] using integral_fintype_prod_eq_pow (ι := Fin n) (fun x => exp (g x))
    rw [hpow]
    have hdiv : ENNReal.ofReal ((∫ x, exp (g x) ∂μ) ^ n) / η =
      ENNReal.ofReal (exp (-c * n) * (∫ x, exp (g x) ∂μ) ^ n) := by
      unfold η
      rw [← ofReal_div_of_pos (exp_pos _)]
      apply congrArg ENNReal.ofReal
      rw [div_eq_mul_inv, ← exp_neg, neg_mul, mul_comm]
    rw [hdiv]
  have integral_exp_indicator (A : Set α) (hA : MeasurableSet A) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ =
      (1 - μ.real A) + μ.real A * exp t := by
    have hfun : (fun x => exp (t * A.indicator (fun _ => (1 : ℝ)) x)) =
      A.indicator (fun _ => exp t) + Aᶜ.indicator (fun _ => (1 : ℝ)) := by
      funext x
      if hx : x ∈ A then
        simp [hx, indicator]
      else
        simp [hx, indicator]
    have hintA : Integrable (A.indicator fun _ => exp t) μ := (integrable_const _).indicator hA
    have hintc : Integrable (Aᶜ.indicator fun _ => (1 : ℝ)) μ :=
      (integrable_const _).indicator hA.compl
    rw [hfun]
    have hpoint : (A.indicator (fun _ => exp t) + Aᶜ.indicator (fun _ => (1 : ℝ))) =
      fun x => A.indicator (fun _ => exp t) x + Aᶜ.indicator (fun _ => (1 : ℝ)) x := rfl
    rw [hpoint, integral_add hintA hintc]
    rw [integral_indicator_const (exp t) hA]
    rw [integral_indicator_const (1 : ℝ) hA.compl, smul_eq_mul, smul_eq_mul, mul_one]
    have hcompl : μ.real Aᶜ = 1 - μ.real A := by
      have hsub : μ Aᶜ = μ Set.univ - μ A := measure_compl hA (measure_ne_top μ A)
      rw [measure_univ] at hsub
      have hle : μ A ≤ μ Set.univ := measure_mono (subset_univ A)
      rw [measure_univ] at hle
      rw [show μ.real Aᶜ = (μ Aᶜ).toReal from rfl, hsub, ENNReal.toReal_sub_of_le hle one_ne_top]
      rfl
    rw [hcompl]
    ring
  have integral_indicator_emp {n : ℕ} (ω : Fin n → α) (A : Set α)
    (hA : MeasurableSet A) :
    ∫ x, A.indicator (1 : α → ℝ) x ∂((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i)) =
      (∑ i, A.indicator (1 : α → ℝ) (ω i)) / n := by
    have hf : StronglyMeasurable (A.indicator (1 : α → ℝ)) :=
      (measurable_const.indicator hA).stronglyMeasurable
    rw [integral_smul_measure]
    have hint : ∀ i ∈ Finset.univ,
      Integrable (A.indicator (1 : α → ℝ)) (Measure.dirac (ω i)) :=
      fun _ _ => integrable_dirac' hf (by finiteness)
    rw [integral_finsetSum_measure hint]
    have hsum : ∑ i, ∫ x, A.indicator (1 : α → ℝ) x ∂Measure.dirac (ω i) =
      ∑ i, A.indicator (1 : α → ℝ) (ω i) := by
      refine Finset.sum_congr rfl fun i _ => integral_dirac' _ (ω i) hf
    rw [hsum, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul]
  have massBound (A : Set α) (hA : MeasurableSet A) (ε : NNReal) (R : ℝ)
    (hε : 0 < (ε : ℝ)) (hR : 0 ≤ R) (hq : μ.real A ≤ Real.exp (-((R + 1) / (ε : ℝ))))
    (n : ℕ) (hn : 0 < n) :
    law n {ν | ε < ν A} ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * R)) := by
    let t : ℝ := (R + 1) / (ε : ℝ)
    have ht : 0 < t := div_pos (by linarith) hε
    let G : Set (ProbabilityMeasure α) := {ν | (ε : ℝ) ≤ (ν : Measure α).real A}
    have hsub : {ν | ε < ν A} ⊆ G := by
      intro ν hν
      simp only [mem_ofPred_eq, G, measureReal_eq_coe_coeFn] at hν ⊢
      exact hν.le
    have hG : MeasurableSet G := by
      have heq : G = (fun ν : ProbabilityMeasure α => (ν : Measure α).real A) ⁻¹' Ici (ε : ℝ) := by
        ext ν
        simp [G]
      rw [heq]
      exact (measurable_toReal.comp
        ((Measure.measurable_coe hA).comp measurable_subtype_coe)) measurableSet_Ici
    have hemp : Measurable (emp n) := by
      let rhs : (Fin n → α) → ProbabilityMeasure α :=
        fun ω => (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
          IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
      suffices heq : emp n = rhs from heq ▸ Measurable.of.Gt_0 (α := α) hn
      funext ω
      unfold emp
      exact dite_eq_left hn
    have hmono : law n {ν | ε < ν A} ≤ law n G := measure_mono hsub
    refine hmono.trans ?_
    have hmap : law n G =
      (Measure.pi fun _ : Fin n => μ) ((emp n : (Fin n → α) → ProbabilityMeasure α) ⁻¹' G) := by
      simpa [law] using Measure.map_apply hemp hG
    rw [hmap]
    have hpre : (emp n : (Fin n → α) → ProbabilityMeasure α) ⁻¹' G ⊆
      {ω | (ε : ℝ) * n ≤ ∑ i, A.indicator (fun _ => (1 : ℝ)) (ω i)} := by
      intro ω hω
      have hmem : (ε : ℝ) ≤ ((emp n ω : ProbabilityMeasure α) : Measure α).real A := by
        simpa [G] using hω
      have hcoe : ((emp n ω : ProbabilityMeasure α) : Measure α) =
        (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i) := by
        have hempω : emp n ω =
          (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
            IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α) := by
          unfold emp
          exact dite_eq_left hn
        rw [hempω]
        rfl
      rwa [hcoe, ← integral_indicator_one hA, integral_indicator_emp ω A hA,
        le_div_iff₀ (Nat.cast_pos.mpr hn)] at hmem
    refine (measure_mono hpre).trans ?_
    refine (indicatorChernoff A hA t (ε : ℝ) ht n).trans ?_
    have hIeq := integral_exp_indicator A hA t ht.le
    have hcancel : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    have hI : ∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ ≤ 2 := by
      rw [hIeq]
      have hq' : μ.real A * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
        mul_le_mul_of_nonneg_right hq (exp_pos t).le
      rw [hcancel] at hq'
      have hq0 : 0 ≤ μ.real A := measureReal_nonneg
      linarith
    have hIpos : 0 < ∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ := by
      rw [hIeq]
      have hq0 : 0 ≤ μ.real A := measureReal_nonneg
      have hexp : 1 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
      have hmul : μ.real A * 1 ≤ μ.real A * Real.exp t := mul_le_mul_of_nonneg_left hexp hq0
      linarith
    have hlogI : Real.log (∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ) ≤ Real.log 2 :=
      Real.log_le_log hIpos hI
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      linarith [Real.add_one_le_exp 1]
    have hrate : -(t * (ε : ℝ)) +
      Real.log (∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ) ≤ -R := by
      have htε : t * (ε : ℝ) = R + 1 := by
        simp only [t]
        exact div_mul_cancel₀ _ hε.ne'
      linarith
    have hpow : exp (-(t * (ε : ℝ)) * n) *
      (∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ) ^ n =
      exp ((n : ℝ) * (-(t * (ε : ℝ)) +
        Real.log (∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ))) := by
      have hlogpow : (∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ) ^ n =
        exp ((n : ℝ) * Real.log (∫ x, exp (t * A.indicator (fun _ => (1 : ℝ)) x) ∂μ)) := by
        nth_rw 1 [← Real.exp_log hIpos]
        rw [← Real.exp_nat_mul]
      rw [hlogpow, ← Real.exp_add]
      congr 1
      ring
    rw [hpow]
    refine ofReal_le_ofReal ?_
    refine exp_le_exp.mpr ?_
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have := mul_le_mul_of_nonneg_left hrate hn0
    linarith
  have law_univ (n : ℕ) : law n Set.univ = 1 := by
    have hemp : Measurable (emp n) := by
      if hn : 0 < n then
        let rhs : (Fin n → α) → ProbabilityMeasure α :=
          fun ω => (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
            IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
        suffices heq : emp n = rhs from heq ▸ Measurable.of.Gt_0 (α := α) hn
        funext ω
        unfold emp
        exact dite_eq_left hn
      else
        suffices heq : emp n = fun _ => μ.toProbabilityMeasure from heq ▸ measurable_const
        funext ω
        unfold emp
        exact dite_eq_right hn
    unfold law
    rw [Measure.map_apply hemp MeasurableSet.univ, Set.preimage_univ, measure_univ]
  if hM : M ≤ 0 then
    refine ⟨∅, isCompact_empty, ?_⟩
    have hev : ∀ᶠ n in atTop, ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n ∅ᶜ) = 0 := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [Set.compl_empty, law_univ n, ENNReal.log_one, mul_zero]
    rw [Filter.limsup_congr hev, Filter.limsup_const, ← EReal.coe_neg]
    exact EReal.coe_nonneg.mpr (neg_nonneg.mpr hM)
  else
    push Not at hM
    let ε : ℕ → NNReal := fun j => (1 / 2 : NNReal) ^ (j + 1)
    let R : ℕ → ℝ := fun j => M + (j + 1)
    have hεpos : ∀ j, 0 < (ε j : ℝ) := fun j => by
      exact NNReal.coe_pos.mpr (pow_pos (by norm_num : (0 : NNReal) < 1 / 2) _)
    have hRpos : ∀ j, 0 ≤ R j := fun j => by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      simp only [R]
      linarith
    have hεlim : Tendsto ε atTop (𝓝 0) := by
      have hpow : Tendsto (fun j : ℕ => ((1 : NNReal) / 2) ^ j) atTop (𝓝 0) := by
        rw [NNReal.tendsto_pow_atTop_nhds_zero_iff]
        norm_num
      have heq : ε = fun j => (1 / 2 : NNReal) * (1 / 2 : NNReal) ^ j := by
        funext j
        simp only [ε, pow_succ, mul_comm]
      rw [heq]
      simpa using hpow.const_mul (1 / 2 : NNReal)
    have hex : ∀ j, ∃ K : Set α, IsCompact K ∧ IsClosed K ∧
      μ Kᶜ < ENNReal.ofReal (Real.exp (-((R j + 1) / (ε j : ℝ)))) := by
      intro j
      let := TopologicalSpace.upgradeIsCompletelyMetrizable α
      let δ := ENNReal.ofReal (Real.exp (-((R j + 1) / (ε j : ℝ))))
      have hδ : δ ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      obtain ⟨K, -, hKco, hKcl, hKμ⟩ :=
        MeasurableSet.univ.exists_isCompact_isClosed_lt_add (μ := μ) (measure_ne_top μ _) hδ
      refine ⟨K, hKco, hKcl, ?_⟩
      rw [measure_compl hKcl.measurableSet (measure_ne_top μ K)]
      exact ENNReal.sub_lt_of_lt_add (measure_mono (subset_univ K)) (by simpa [δ, add_comm] using hKμ)
    choose C hCco hCcl hCμ using hex
    let L : ℕ → Set α := fun j => ⋃ i ∈ Finset.range (j + 1), C i
    have hLco : ∀ j, IsCompact (L j) := fun j =>
      (Finset.range (j + 1)).isCompact_biUnion fun i _ => hCco i
    have hLcl : ∀ j, IsClosed (L j) := fun j =>
      isClosed_biUnion_finset fun i _ => hCcl i
    have hmono : Monotone L := monotone_nat_of_le_succ fun j => by
      intro x hx
      simp only [L, mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hxi⟩ := hx
      refine ⟨i, ?_, hxi⟩
      simp only [Finset.mem_range] at hi ⊢
      omega
    have hCj : ∀ j, C j ⊆ L j := by
      intro j x hx
      simp only [L, mem_iUnion]
      exact ⟨j, by simp, hx⟩
    have hLreal : ∀ j, μ.real (L j)ᶜ ≤ Real.exp (-((R j + 1) / (ε j : ℝ))) := by
      intro j
      have hsub : (L j)ᶜ ⊆ (C j)ᶜ := compl_subset_compl.mpr (hCj j)
      have hlt : μ (L j)ᶜ < ENNReal.ofReal (Real.exp (-((R j + 1) / (ε j : ℝ)))) :=
        (measure_mono hsub).trans_lt (hCμ j)
      have hle := (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hlt.le
      simpa [measureReal_def, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hle
    let Γ : Set (ProbabilityMeasure α) := {ν | ∀ j, ν (L j)ᶜ ≤ ε j}
    have hΓ : IsCompact Γ :=
      isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le hεlim hLco (Or.inr hmono)
    let f : ℕ → ℝ := fun j => Real.exp (-((j : ℝ) + 1))
    have hfsum : Summable f := by
      have heq : f = fun j => Real.exp (-1) * (Real.exp (-1)) ^ j := by
        funext j
        simp only [f]
        rw [show -((j : ℝ) + 1) = (j : ℝ) * (-1) + (-1) by ring, Real.exp_add, Real.exp_nat_mul]
        ring
      have hlt : Real.exp (-1) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      rw [heq]
      exact (summable_geometric_of_lt_one (Real.exp_nonneg _) hlt).mul_left _
    let S : ℝ≥0∞ := ∑' j, ENNReal.ofReal (f j)
    have hSne : S ≠ ⊤ := hfsum.tsum_ofReal_ne_top
    have hSpos : 0 < S := by
      refine lt_of_lt_of_le ?_ (ENNReal.le_tsum (f := fun j => ENNReal.ofReal (f j)) 0)
      simpa [f] using ENNReal.ofReal_pos.mpr (Real.exp_pos (-1))
    have hsubΓ : Γᶜ ⊆ ⋃ j, {ν | ε j < ν (L j)ᶜ} := by
      intro ν hν
      simp only [Γ, mem_compl_iff, mem_ofPred_eq, not_forall] at hν
      obtain ⟨j, hj⟩ := hν
      exact mem_iUnion.mpr ⟨j, lt_of_not_ge hj⟩
    have hmass : ∀ n, 0 < n → law n Γᶜ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * M)) * S := by
      intro n hn
      have hterm : ∀ j, law n {ν | ε j < ν (L j)ᶜ} ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) * M)) * ENNReal.ofReal (f j) := by
        intro j
        refine (massBound (L j)ᶜ (hLcl j).measurableSet.compl (ε j) (R j)
          (hεpos j) (hRpos j) (hLreal j) n hn).trans ?_
        have hsplit : Real.exp (-(n : ℝ) * R j) =
          Real.exp (-(n : ℝ) * M) * Real.exp (-(n : ℝ) * ((j : ℝ) + 1)) := by
          rw [← Real.exp_add]
          congr 1
          simp only [R]
          ring
        have hsmall : Real.exp (-(n : ℝ) * ((j : ℝ) + 1)) ≤ f j := by
          refine Real.exp_le_exp.mpr ?_
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        rw [hsplit, ENNReal.ofReal_mul (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hsmall) (by positivity)
      refine (measure_mono hsubΓ).trans ((measure_iUnion_le _).trans ?_)
      refine (ENNReal.tsum_le_tsum hterm).trans ?_
      rw [ENNReal.tsum_mul_left]
    have hstep : ∀ n, 1 ≤ n →
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n Γᶜ) ≤
        -↑M + ((n : ℕ) : EReal)⁻¹ * ENNReal.log S := by
      intro n hn
      have hn0 : 0 < n := by omega
      have hlog := ENNReal.log_le_log (hmass n hn0)
      have hnn : 0 ≤ ((n : ℕ) : EReal) := by exact_mod_cast Nat.zero_le n
      refine (mul_le_mul_of_nonneg_left hlog (EReal.inv_nonneg_of_nonneg hnn)).trans ?_
      rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
        EReal.left_distrib_of_nonneg_of_ne_top (EReal.inv_nonneg_of_nonneg hnn)
          (EReal.inv_lt_top _).ne]
      have hmulM : ((n : ℕ) : EReal)⁻¹ * ↑(-(n : ℝ) * M) = -↑M := by
        rw [← EReal.coe_coe_eq_natCast n, ← EReal.coe_inv (n : ℝ), ← EReal.coe_mul, ← EReal.coe_neg]
        congr 1
        field_simp
      rw [hmulM]
    have hvan : Tendsto (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log S) atTop (𝓝 0) := by
      have hlogS : ENNReal.log S = (Real.log S.toReal : EReal) :=
        ENNReal.log_pos_real hSpos.ne' hSne
      rw [hlogS]
      have hreal : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log S.toReal) atTop (𝓝 0) := by
        simpa [zero_mul] using
          (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (Real.log S.toReal)
      refine (tendsto_congr' ?_).mpr (EReal.tendsto_coe.mpr hreal)
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [← EReal.coe_coe_eq_natCast n, ← EReal.coe_inv (n : ℝ), ← EReal.coe_mul]
    have hconst : Tendsto (fun _ : ℕ => (-↑M : EReal)) atTop (𝓝 (-↑M)) := tendsto_const_nhds
    have hev : ∀ᶠ n in atTop,
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n Γᶜ) ≤
        -↑M + ((n : ℕ) : EReal)⁻¹ * ENNReal.log S := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact hstep n hn
    refine ⟨Γ, hΓ, ?_⟩
    refine (limsup_le_limsup hev).trans ?_
    refine (EReal.limsup_add_le ?_ ?_).trans ?_
    · exact Or.inl (by rw [hconst.limsup_eq, ← EReal.coe_neg]; exact EReal.coe_ne_bot _)
    · exact Or.inl (by rw [hconst.limsup_eq, ← EReal.coe_neg]; exact EReal.coe_ne_top _)
    · rw [hconst.limsup_eq, hvan.limsup_eq, add_zero]

private lemma closedBound
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {F : Set (ProbabilityMeasure α)}
-- given
  (hF : IsClosed F) :
-- imply
  limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
    ((@Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
      (fun ω => if hn : 0 < n then
        (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
          IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
      else μ.toProbabilityMeasure)
      (Measure.pi fun _ : Fin n => μ)) F)) atTop ≤
    -(⨅ ν ∈ F, (klDiv (ν : Measure α) μ : EReal)) := by
-- proof
  let emp (n : ℕ) (ω : Fin n → α) : ProbabilityMeasure α :=
    if hn : 0 < n then
      (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
        IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
    else
      μ.toProbabilityMeasure
  let law (n : ℕ) : Measure (ProbabilityMeasure α) :=
    @Measure.map (Fin n → α) (ProbabilityMeasure α) _ _ (emp n)
      (Measure.pi fun _ : Fin n => μ)
  let β : EReal := ⨅ ν ∈ F, (klDiv (ν : Measure α) μ : EReal)
  change limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n F)) atTop ≤ -β
  apply Le_Neg.of.All_Le_Neg
  intro t ht
  obtain ⟨Γ, hΓ, hΓc⟩ := tight (μ := μ) t
  let K := Γ ∩ F
  have hK : IsCompact K := hΓ.inter_right hF
  have hsub : F ⊆ K ∪ Γᶜ := by
    intro ν hν
    if hΓν : ν ∈ Γ then
      exact Or.inl ⟨hΓν, hν⟩
    else
      exact Or.inr hΓν
  have hle : ∀ n, law n F ≤ law n K + law n Γᶜ := fun n =>
    (measure_mono hsub).trans (measure_union_le _ _)
  have hsplit : ∀ n, 1 ≤ n →
    ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n F) ≤
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log 2 +
        max (((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K))
          (((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n Γᶜ)) := by
    intro n hn
    have hnn : 0 ≤ ((n : ℕ) : EReal) := by exact_mod_cast Nat.zero_le n
    have hsum : law n F ≤ 2 * max (law n K) (law n Γᶜ) := calc
      _ ≤ law n K + law n Γᶜ := hle n
      _ ≤ max (law n K) (law n Γᶜ) + max (law n K) (law n Γᶜ) :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max (law n K) (law n Γᶜ) := by rw [two_mul]
    have hlog := ENNReal.log_le_log hsum
    rw [ENNReal.log_mul_add] at hlog
    have hmax : ENNReal.log (max (law n K) (law n Γᶜ)) =
      max (ENNReal.log (law n K)) (ENNReal.log (law n Γᶜ)) := by
      if h : law n K ≤ law n Γᶜ then
        rw [max_eq_right h, max_eq_right (ENNReal.log_le_log h)]
      else
        have h' : law n Γᶜ ≤ law n K := le_of_not_ge h
        rw [max_eq_left h', max_eq_left (ENNReal.log_le_log h')]
    rw [hmax] at hlog
    refine (mul_le_mul_of_nonneg_left hlog (EReal.inv_nonneg_of_nonneg hnn)).trans (le_of_eq ?_)
    rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.inv_nonneg_of_nonneg hnn)
      (EReal.inv_lt_top _).ne]
    if hlogle : ENNReal.log (law n K) ≤ ENNReal.log (law n Γᶜ) then
      rw [max_eq_right hlogle, max_eq_right
        (mul_le_mul_of_nonneg_left hlogle (EReal.inv_nonneg_of_nonneg hnn))]
    else
      have hlogle' : ENNReal.log (law n Γᶜ) ≤ ENNReal.log (law n K) := le_of_not_ge hlogle
      rw [max_eq_left hlogle', max_eq_left
        (mul_le_mul_of_nonneg_left hlogle' (EReal.inv_nonneg_of_nonneg hnn))]
  have hKlim : limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K)) atTop ≤
    -(⨅ ν ∈ K, (klDiv (ν : Measure α) μ : EReal)) := by
    unfold law emp
    exact Limsup_MulInvERealLog.le.NegIn.inf.KlDivMeasure.of.IsCompact (μ := μ) hK
  have hKβ : -(⨅ ν ∈ K, (klDiv (ν : Measure α) μ : EReal)) ≤ -β :=
    EReal.neg_le_neg_iff.mpr (le_iInf₂ fun (ν : ProbabilityMeasure α) (hν : ν ∈ K) =>
      iInf₂_le (f := fun (ρ : ProbabilityMeasure α) (_ : ρ ∈ F) =>
        (klDiv (ρ : Measure α) μ : EReal)) ν hν.2)
  have htβ : -β ≤ -↑t := EReal.neg_le_neg_iff.mpr ht.le
  have hlog2 : Tendsto (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (2 : ℝ≥0∞)) atTop (𝓝 0) := by
    have hlogc : ENNReal.log (2 : ℝ≥0∞) = (Real.log 2 : EReal) := by
      rw [ENNReal.log_pos_real (by norm_num) (by simp), ENNReal.toReal_ofNat]
    rw [hlogc]
    have hreal : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log 2) atTop (𝓝 0) := by
      simpa [zero_mul] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (Real.log 2)
    refine (tendsto_congr' ?_).mpr (EReal.tendsto_coe.mpr hreal)
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← EReal.coe_coe_eq_natCast n, ← EReal.coe_inv (n : ℝ), ← EReal.coe_mul]
  have hev : ∀ᶠ n in atTop,
    ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n F) ≤
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log (2 : ℝ≥0∞) +
        max (((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n K))
          (((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n Γᶜ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hsplit n hn
  refine (limsup_le_limsup hev).trans ?_
  refine (EReal.limsup_add_le ?_ ?_).trans ?_
  · exact Or.inl (by simp [hlog2.limsup_eq])
  · exact Or.inl (by simp [hlog2.limsup_eq])
  rw [hlog2.limsup_eq, zero_add, limsup_max]
  refine max_le ?_ ?_
  · exact hKlim.trans (hKβ.trans htβ)
  · exact hΓc

/--
On a Polish space, the empirical measures of i.i.d. samples satisfy the large deviation principle
of speed `n` with rate the Kullback–Leibler divergence from the common law.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ] :
-- imply
  SatisfiesLDP
    (fun n =>
      @Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
        (fun ω => if hn : 0 < n then
          (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
            IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
        else μ.toProbabilityMeasure)
        (Measure.pi fun _ : Fin n => μ))
    (fun ν : ProbabilityMeasure α => klDiv (ν : Measure α) μ) := by
-- proof
  refine ⟨⟨LowerSemicontinuous_KlDivMeasure (μ := μ)⟩,
    fun U hU => NegIn.inf.KlDivMeasure.le.Liminf_MulInvERealLog.of.IsOpen (μ := μ) hU,
    fun F hF => closedBound (μ := μ) hF⟩


-- created on 2026-11-03
-- updated on 2026-11-05
