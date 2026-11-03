import Lemma.Random.Any_ContinuousAndAny_All_LeAbsAndLeSubToRealIntegral_Sub_Log.of.Lt0
import Lemma.Random.KlDiv.eq.All_EqGetMap0.of.Measurable
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Int
import Initialize.Tactic.Attr.Basic
open ENNReal Filter Finset InformationTheory MeasureTheory Random Real Set


private lemma kl_nonneg [Fintype ι] (p m : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, 0 ≤ m i) (hsump : ∑ i, p i = 1) (hsumm : ∑ i, m i = 1) (hsup : ∀ i, m i = 0 → p i = 0) : 0 ≤ ∑ i, p i * log (p i / m i) := by
  have hterm : ∀ i, p i - m i ≤ p i * log (p i / m i) := by
    intro i
    obtain h0 | hpos := eq_or_lt_of_le (hp i)
    ·
      rw [← h0]
      simp
      linarith [hm i]
    ·
      have hmpos : 0 < m i := lt_of_le_of_ne (hm i) fun h => hpos.ne' (hsup i h.symm)
      have hineq := log_le_sub_one_of_pos (div_pos hmpos hpos)
      have hmul := mul_le_mul_of_nonneg_left hineq hpos.le
      have hright : p i * (m i / p i - 1) = m i - p i := by
        field_simp [hpos.ne']
      have hlog : p i * log (p i / m i) = -(p i * log (m i / p i)) := by
        rw [← inv_div, log_inv (m i / p i), mul_neg]
      rw [hlog]
      rw [hright] at hmul
      linarith
  calc
    _ = ∑ i, p i - ∑ i, m i := by simp [hsump, hsumm]
    _ = ∑ i, (p i - m i) := by rw [← sum_sub_distrib]
    _ ≤ ∑ i, p i * log (p i / m i) := sum_le_sum fun i _ => hterm i

private lemma expr_le_kl [Fintype ι] (c p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hsump : ∑ i, p i = 1) (hsumq : ∑ i, q i = 1) (hsup : ∀ i, q i = 0 → p i = 0) : ∑ i, c i * p i - log (∑ i, exp (c i) * q i) ≤ ∑ i, p i * log (p i / q i) := by
  let Z := ∑ i, exp (c i) * q i
  have hZ : 0 < Z := by
    have hex : ∃ j, 0 < q j := by
      by_contra h
      push Not at h
      have hq0 : ∀ j, q j = 0 := fun j => le_antisymm (h j) (hq j)
      have : ∑ i, q i = 0 := by simp [hq0]
      linarith
    obtain ⟨j, hj⟩ := hex
    exact lt_of_lt_of_le (mul_pos (exp_pos _) hj)
      (single_le_sum (fun i _ => mul_nonneg (exp_pos _).le (hq i)) (mem_univ j))
  let r : ι → ℝ := fun i => exp (c i) * q i / Z
  have hr0 : ∀ i, 0 ≤ r i := fun i => div_nonneg (mul_nonneg (exp_pos _).le (hq i)) hZ.le
  have hsumr : ∑ i, r i = 1 := by
    simp only [r]
    rw [← Finset.sum_div, div_self hZ.ne']
  have hpr : ∀ i, r i = 0 → p i = 0 := by
    intro i hi
    exact hsup i ((mul_eq_zero.mp ((div_eq_zero_iff.mp hi).resolve_right hZ.ne')).resolve_left
      (exp_pos _).ne')
  have hterm : ∀ i, p i * log (p i / q i) - c i * p i + p i * log Z = p i * log (p i / r i) := by
    intro i
    obtain h0 | hpos := eq_or_lt_of_le (hp i)
    ·
      rw [← h0]
      simp
    ·
      have hqpos : 0 < q i := lt_of_le_of_ne (hq i) fun h => hpos.ne' (hsup i h.symm)
      have hrpos : 0 < r i := div_pos (mul_pos (exp_pos _) hqpos) hZ
      have hlogR : log (r i) = c i + log (q i) - log Z := by
        simp only [r]
        rw [log_div (mul_pos (exp_pos _) hqpos).ne' hZ.ne', log_mul (exp_pos _).ne' hqpos.ne',
          log_exp]
      calc
        _ = p i * (log (p i / q i) - c i + log Z) := by ring
        _ = p i * log (p i / r i) := by
          congr 1
          rw [log_div hpos.ne' hqpos.ne', log_div hpos.ne' hrpos.ne', hlogR]
          ring
  have hfactor : log Z = ∑ i, p i * log Z := by
    have hmul : (∑ i, p i) * log Z = ∑ i, p i * log Z :=
      Finset.sum_mul univ (fun i => p i) (log Z)
    calc
      _ = 1 * log Z := by ring
      _ = (∑ i, p i) * log Z := by rw [hsump]
      _ = ∑ i, p i * log Z := hmul
  have hdiff : ∑ i, p i * log (p i / q i) - (∑ i, c i * p i - log Z) = ∑ i, p i * log (p i / r i) := calc
    _ = ∑ i, p i * log (p i / q i) - ∑ i, c i * p i + log Z := by ring
    _ = ∑ i, (p i * log (p i / q i) - c i * p i) + log Z := by rw [← sum_sub_distrib]
    _ = ∑ i, (p i * log (p i / q i) - c i * p i) + ∑ i, p i * log Z := by
      conv_lhs => rw [hfactor]
    _ = ∑ i, (p i * log (p i / q i) - c i * p i + p i * log Z) := by rw [← sum_add_distrib]
    _ = ∑ i, p i * log (p i / r i) := sum_congr rfl fun i _ => hterm i
  have hnonneg := kl_nonneg p r hp hr0 hsump hsumr hpr
  linarith [hdiff]

/--
On a Polish space, a finite Kullback–Leibler divergence is nearly realized by a measurable map
into a finite set of integers. The divergence of the pushed-forward probabilities is the entropy
of one finite partition, and it comes within any positive tolerance of the original divergence.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℝ}
-- given
  (hfin : klDiv ν μ ≠ ⊤)
  (hε : 0 < ε) :
-- imply
  ∃ s : Finset ℤ, ∃ φ : α → s, Measurable φ ∧
    (klDiv ν μ).toReal - ε ≤ (klDiv (ν.map φ) (μ.map φ)).toReal :=
-- proof
by
  have hsplit := (klDiv_ne_top_iff (μ := ν) (ν := μ)).mp hfin
  obtain ⟨g, hg, ⟨C0, hC0⟩, hge⟩ :=
    Any_ContinuousAndAny_All_LeAbsAndLeSubToRealIntegral_Sub_Log.of.Lt0 hsplit.1 hsplit.2
      (half_pos hε)
  let C := max C0 0
  have hCnonneg : 0 ≤ C := le_max_right _ _
  have hC : ∀ x, |g x| ≤ C := fun x => le_trans (hC0 x) (le_max_left _ _)
  let B := 1 + exp (2 * C + 2)
  have hB : 0 < B := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (B / (ε / 2))
  have hn0 : (0 : ℝ) < n := lt_trans (div_pos hB (by linarith)) hn
  have hBn : B / n < ε / 2 := by
    rw [div_lt_iff₀ hn0]
    have hden : 0 < ε / 2 := by linarith
    rw [div_lt_iff₀ hden] at hn
    linarith
  let f : α → ℝ := fun x => (⌊(n : ℝ) * g x⌋ : ℝ) / n
  have hgf : ∀ x, g x - f x = ((n : ℝ) * g x - ↑⌊(n : ℝ) * g x⌋) / n := by
    intro x
    simp only [f]
    rw [sub_div, mul_div_cancel_left₀ _ hn0.ne']
  have hclose : ∀ x, 0 ≤ g x - f x ∧ g x - f x ≤ 1 / n := by
    intro x
    have hfract₀ : 0 ≤ (n : ℝ) * g x - ↑⌊(n : ℝ) * g x⌋ := by
      linarith [Int.floor_le ((n : ℝ) * g x)]
    have hfract₁ : (n : ℝ) * g x - ↑⌊(n : ℝ) * g x⌋ ≤ 1 := by
      linarith [Int.lt_floor_add_one ((n : ℝ) * g x)]
    constructor
    ·
      rw [hgf]
      exact div_nonneg hfract₀ hn0.le
    ·
      rw [hgf]
      exact div_le_div_of_nonneg_right hfract₁ hn0.le
  have hf_bound : ∀ x, |f x| ≤ C + 1 := by
    intro x
    have hgabs := abs_le.mp (hC x)
    have hinv : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]
      exact_mod_cast Nat.one_le_of_lt (Nat.cast_pos.mp hn0)
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [(hclose x).2, hgabs.1]
    · linarith [(hclose x).1, hgabs.2]
  have hf_meas : Measurable f := by
    exact (continuous_of_discreteTopology.measurable.comp
      (hg.measurable.const_mul (n : ℝ)).floor).div_const _
  have hg_int : Integrable g ν :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  have hf_int : Integrable f ν :=
    Integrable.of_bound hf_meas.aestronglyMeasurable (C + 1) (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hf_bound x)
  have hexpg_int : Integrable (fun x => exp (g x)) μ :=
    Integrable.of_bound (hg.measurable.exp).aestronglyMeasurable (exp C)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr (abs_le.mp (hC x)).2)
  have hexpf_int : Integrable (fun x => exp (f x)) μ :=
    Integrable.of_bound (hf_meas.exp).aestronglyMeasurable (exp (C + 1))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr (abs_le.mp (hf_bound x)).2)
  have hint_sub : ∫ x, g x ∂ν - ∫ x, f x ∂ν ≤ 1 / n := by
    rw [← integral_sub hg_int hf_int]
    have hmono := integral_mono (hg_int.sub hf_int) (integrable_const ((1 : ℝ) / n)) fun x => (hclose x).2
    simpa [integral_const, probReal_univ, smul_eq_mul, one_mul] using hmono
  let Ig := ∫ x, exp (g x) ∂μ
  let Ie := ∫ x, exp (f x) ∂μ
  have habs_int : |Ig - Ie| ≤ exp (C + 1) / n := by
    have hlip : ∀ a b, |a| ≤ C + 1 → |b| ≤ C + 1 →
        |exp a - exp b| ≤ exp (C + 1) * |a - b| := by
      intro a b ha hb
      have hderiv : ∀ x ∈ interior (Icc (-(C + 1)) (C + 1)), deriv exp x ≤ exp (C + 1) := by
        intro x hx
        rw [interior_Icc] at hx
        rw [Real.deriv_exp]
        exact exp_le_exp.mpr (le_of_lt hx.2)
      have hgrow := (convex_Icc (-(C + 1)) (C + 1)).image_sub_le_mul_sub_of_deriv_le
        continuous_exp.continuousOn differentiable_exp.differentiableOn hderiv
      obtain hab | hba := le_total a b
      ·
        have hmem_a : a ∈ Icc (-(C + 1)) (C + 1) := abs_le.mp ha
        have hmem_b : b ∈ Icc (-(C + 1)) (C + 1) := abs_le.mp hb
        have hdiff := hgrow a hmem_a b hmem_b hab
        rw [abs_sub_comm (exp a), abs_sub_comm a]
        rw [abs_of_nonneg (sub_nonneg.mpr (exp_le_exp.mpr hab)), abs_of_nonneg (sub_nonneg.mpr hab)]
        exact hdiff
      ·
        have hmem_a : a ∈ Icc (-(C + 1)) (C + 1) := abs_le.mp ha
        have hmem_b : b ∈ Icc (-(C + 1)) (C + 1) := abs_le.mp hb
        have hdiff := hgrow b hmem_b a hmem_a hba
        rw [abs_of_nonneg (sub_nonneg.mpr (exp_le_exp.mpr hba)), abs_of_nonneg (sub_nonneg.mpr hba)]
        exact hdiff
    have hpoint : ∀ x, |exp (g x) - exp (f x)| ≤ exp (C + 1) / n := by
      intro x
      have hgabs : |g x| ≤ C + 1 := le_trans (hC x) (by linarith)
      calc
        _ ≤ exp (C + 1) * |g x - f x| := hlip (g x) (f x) hgabs (hf_bound x)
        _ ≤ exp (C + 1) * (1 / n) := by
          gcongr
          rw [abs_of_nonneg (hclose x).1]
          exact (hclose x).2
        _ = exp (C + 1) / n := by ring
    have hnorm := norm_integral_le_of_norm_le (μ := μ) (integrable_const (exp (C + 1) / (n : ℝ)))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hpoint x)
    have hsub : ∫ x, (exp (g x) - exp (f x)) ∂μ = Ig - Ie := by
      rw [integral_sub hexpg_int hexpf_int]
    rw [← hsub]
    simpa [integral_const, probReal_univ, smul_eq_mul, one_mul, Real.norm_eq_abs] using hnorm
  have hexp_ge : exp (-(C + 1)) ≤ Ig ∧ exp (-(C + 1)) ≤ Ie := by
    constructor
    ·
      have hmono := integral_mono (integrable_const _) hexpg_int fun x =>
        exp_le_exp.mpr (le_trans (by linarith : -(C + 1) ≤ -C) (abs_le.mp (hC x)).1)
      simpa [integral_const, probReal_univ, smul_eq_mul, one_mul] using hmono
    ·
      have hmono := integral_mono (integrable_const _) hexpf_int fun x =>
        exp_le_exp.mpr (abs_le.mp (hf_bound x)).1
      simpa [integral_const, probReal_univ, smul_eq_mul, one_mul] using hmono
  have hlog_lip : |log Ig - log Ie| ≤ exp (C + 1) * |Ig - Ie| := by
    have hm : 0 < exp (-(C + 1)) := exp_pos _
    have hIg : 0 < Ig := lt_of_lt_of_le hm hexp_ge.1
    have hIe : 0 < Ie := lt_of_lt_of_le hm hexp_ge.2
    have hinv : ∀ t, exp (-(C + 1)) ≤ t → 1 / t ≤ exp (C + 1) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hm ht
      rw [div_le_iff₀ ht0]
      have hone : exp (-(C + 1)) * exp (C + 1) = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
      linarith [mul_le_mul_of_nonneg_right ht (exp_pos (C + 1)).le, hone]
    obtain hle | hge' := le_total Ie Ig
    ·
      have hdiv : log Ig - log Ie ≤ (Ig - Ie) / Ie := by
        calc
          log Ig - log Ie = log (Ig / Ie) := by rw [log_div hIg.ne' hIe.ne']
          _ ≤ Ig / Ie - 1 := log_le_sub_one_of_pos (div_pos hIg hIe)
          _ = (Ig - Ie) / Ie := by field_simp
      have hscale : (Ig - Ie) / Ie ≤ exp (C + 1) * (Ig - Ie) := by
        calc
          (Ig - Ie) / Ie = (Ig - Ie) * (1 / Ie) := by field_simp
          _ ≤ (Ig - Ie) * exp (C + 1) :=
            mul_le_mul_of_nonneg_left (hinv Ie hexp_ge.2) (sub_nonneg.mpr hle)
          _ = exp (C + 1) * (Ig - Ie) := by ring
      rw [abs_of_nonneg (sub_nonneg.mpr (log_le_log hIe hle)), abs_of_nonneg (sub_nonneg.mpr hle)]
      linarith
    ·
      have hdiv : log Ie - log Ig ≤ (Ie - Ig) / Ig := by
        calc
          log Ie - log Ig = log (Ie / Ig) := by rw [log_div hIe.ne' hIg.ne']
          _ ≤ Ie / Ig - 1 := log_le_sub_one_of_pos (div_pos hIe hIg)
          _ = (Ie - Ig) / Ig := by field_simp
      have hscale : (Ie - Ig) / Ig ≤ exp (C + 1) * (Ie - Ig) := by
        calc
          (Ie - Ig) / Ig = (Ie - Ig) * (1 / Ig) := by field_simp
          _ ≤ (Ie - Ig) * exp (C + 1) :=
            mul_le_mul_of_nonneg_left (hinv Ig hexp_ge.1) (sub_nonneg.mpr hge')
          _ = exp (C + 1) * (Ie - Ig) := by ring
      rw [abs_sub_comm (log Ig), abs_sub_comm Ig,
        abs_of_nonneg (sub_nonneg.mpr (log_le_log hIg hge')), abs_of_nonneg (sub_nonneg.mpr hge')]
      linarith
  have hexpr : (klDiv ν μ).toReal - ε ≤ ∫ x, f x ∂ν - log Ie := by
    have hloss : 1 / n + exp (C + 1) * |Ig - Ie| ≤ B / n := by
      calc
        _ ≤ 1 / n + exp (C + 1) * (exp (C + 1) / n) := by gcongr
        _ = (1 + exp (C + 1) * exp (C + 1)) / n := by ring
        _ = (1 + exp (2 * C + 2)) / n := by
          rw [← exp_add]
          exact congrArg (fun t => (1 + exp t) / n) (by ring)
        _ = B / n := by simp [B]
    have hlog : -log Ig - exp (C + 1) * |Ig - Ie| ≤ -log Ie := by
      linarith [(abs_le.mp hlog_lip).1]
    apply le_of_lt
    calc
      _ < (klDiv ν μ).toReal - ε / 2 - B / n := by linarith [hBn]
      _ ≤ (klDiv ν μ).toReal - ε / 2 - (1 / n + exp (C + 1) * |Ig - Ie|) := by linarith [hloss]
      _ ≤ ∫ x, g x ∂ν - log Ig - (1 / n + exp (C + 1) * |Ig - Ie|) := by linarith [hge]
      _ ≤ ∫ x, f x ∂ν - log Ie := by linarith [hint_sub, hlog]
  let s : Finset ℤ := Finset.Icc (⌊-(n : ℝ) * C⌋) (⌊(n : ℝ) * C⌋)
  let φ0 : α → ℤ := fun x => ⌊(n : ℝ) * g x⌋
  have hφ0 : Measurable φ0 := (hg.measurable.const_mul (n : ℝ)).floor
  have hmem : ∀ x, φ0 x ∈ s := by
    intro x
    rw [Finset.mem_Icc]
    constructor
    ·
      apply Int.floor_le_floor
      have := mul_le_mul_of_nonneg_left (abs_le.mp (hC x)).1 (Nat.cast_nonneg n)
      simpa [mul_neg] using this
    ·
      exact Int.floor_le_floor (mul_le_mul_of_nonneg_left (abs_le.mp (hC x)).2 (Nat.cast_nonneg n))
  let φ : α → s := fun x => ⟨φ0 x, hmem x⟩
  have hφ : Measurable φ := hφ0.subtype_mk (h := hmem)
  let : IsProbabilityMeasure (ν.map φ) :=
    (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (μ.map φ) :=
    (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  have hdisj : PairwiseDisjoint (↑(univ : Finset s)) (fun a => ({a} : Set s)) :=
    fun a _ b _ hne => disjoint_singleton.mpr hne
  have hsum_apply (ρ : Measure s) [IsProbabilityMeasure ρ] : ∑ a, (ρ {a}).toReal = 1 := by
    have hsum : ∑ a, ρ {a} = 1 := by
      rw [← measure_biUnion_finset (s := (univ : Finset s)) (f := fun a => ({a} : Set s)) hdisj
        (fun a _ => measurableSet_singleton a)]
      rw [show (⋃ a ∈ (univ : Finset s), ({a} : Set s)) = Set.univ by ext a; simp]
      exact measure_univ
    rw [← ENNReal.toReal_sum fun a _ => measure_ne_top ρ {a}, hsum]
    simp
  let c : s → ℝ := fun a => ((a : ℤ) : ℝ) / n
  let p : s → ℝ := fun a => ((ν.map φ) {a}).toReal
  let q : s → ℝ := fun a => ((μ.map φ) {a}).toReal
  have hp0 : ∀ a, 0 ≤ p a := fun _ => ENNReal.toReal_nonneg
  have hq0 : ∀ a, 0 ≤ q a := fun _ => ENNReal.toReal_nonneg
  have hsump : ∑ a, p a = 1 := hsum_apply (ν.map φ)
  have hsumq : ∑ a, q a = 1 := hsum_apply (μ.map φ)
  have hvan : ∀ a, (μ.map φ) {a} = 0 → (ν.map φ) {a} = 0 := by
    intro a ha
    rw [Measure.map_apply hφ (measurableSet_singleton a)] at ha ⊢
    exact hsplit.1 ha
  have hsup : ∀ a, q a = 0 → p a = 0 := by
    intro a ha
    have hiff : ((μ.map φ) {a}).toReal = 0 ↔ (μ.map φ) {a} = 0 ∨ (μ.map φ) {a} = ⊤ :=
      ENNReal.toReal_eq_zero_iff _
    have hμ0 : (μ.map φ) {a} = 0 := (hiff.mp ha).resolve_right (measure_ne_top _ _)
    simp [p, hvan a hμ0]
  have hintf : ∫ x, f x ∂ν = ∑ a, c a * p a := by
    have hgc : AEStronglyMeasurable c (ν.map φ) := (measurable_of_finite c).aestronglyMeasurable
    have hint_c : Integrable c (ν.map φ) :=
      (integrable_map_measure hgc hφ.aemeasurable).2 (by
        have : c ∘ φ = f := by
          funext x
          simp [c, φ, φ0, f]
        simpa [this] using hf_int)
    have hcomp : f = fun x => c (φ x) := by
      funext x
      simp [f, c, φ, φ0]
    rw [hcomp, ← integral_map hφ.aemeasurable hgc, integral_countable hint_c, tsum_fintype]
    refine sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, Measure.real, mul_comm]
  have hintexp : ∫ x, exp (f x) ∂μ = ∑ a, exp (c a) * q a := by
    have hfun : AEStronglyMeasurable (fun a => exp (c a)) (μ.map φ) :=
      (measurable_of_finite (fun a => exp (c a))).aestronglyMeasurable
    have hint_c : Integrable (fun a => exp (c a)) (μ.map φ) :=
      (integrable_map_measure hfun hφ.aemeasurable).2 (by
        have : (fun a => exp (c a)) ∘ φ = fun x => exp (f x) := by
          funext x
          simp [c, φ, φ0, f]
        simpa [this] using hexpf_int)
    have hcomp : (fun x => exp (f x)) = fun x => exp (c (φ x)) := by
      funext x
      simp [f, c, φ, φ0]
    rw [hcomp, ← integral_map hφ.aemeasurable hfun, integral_countable hint_c, tsum_fintype]
    refine sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, Measure.real, mul_comm]
  refine ⟨s, φ, hφ, ?_⟩
  have hkl := KlDiv.eq.All_EqGetMap0.of.Measurable (μ := μ) (ν := ν) hφ
  rw [hkl, ite_eq_left hvan, ENNReal.toReal_ofReal (kl_nonneg p q hp0 hq0 hsump hsumq hsup)]
  calc
    _ ≤ ∫ x, f x ∂ν - log Ie := hexpr
    _ = ∑ a, c a * p a - log (∑ a, exp (c a) * q a) := by
      dsimp only [Ie]
      rw [hintf, hintexp]
    _ ≤ ∑ a, p a * log (p a / q a) := expr_le_kl c p q hp0 hq0 hsump hsumq hsup


-- created on 2026-11-02
