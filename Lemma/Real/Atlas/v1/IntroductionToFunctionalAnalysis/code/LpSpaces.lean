import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.IntroductionToFunctionalAnalysis.code.LpSpaces
open MeasureTheory
open scoped ENNReal NNReal


/--
[eLpNormEssSup_eq_enorm_continuousMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma eLpNormEssSup_eq_enorm_continuousMap
  [TopologicalSpace α]
  [CompactSpace α]
  [MeasurableSpace α]
  [BorelSpace α]
  {μ : Measure α}
  [μ.IsOpenPosMeasure]
  [SeminormedAddCommGroup E]
  {f : C(α, E)} :
-- imply
  eLpNormEssSup (fun x => f x) μ = ‖f‖ₑ := by
-- proof
  simp only [eLpNormEssSup]
  set g : α → ENNReal := fun x => ‖f x‖ₑ
  have hcont : Continuous g := continuous_enorm.comp f.continuous
  have h_essSup_eq : essSup g μ = ⨆ x, g x := by
    apply le_antisymm
    · exact essSup_le_of_ae_le _ (by filter_upwards with x; exact le_iSup g x)
    · apply iSup_le
      intro x
      by_contra h
      simp only [not_le] at h
      have hopen : IsOpen {y | essSup g μ < g y} := hcont.isOpen_preimage _ isOpen_Ioi
      have hpos := hopen.measure_pos μ ⟨x, h⟩
      have hzero : μ {y | essSup g μ < g y} = 0 :=
        measure_mono_null (fun y hy => not_le.mpr hy) (ae_iff.mp (ae_le_essSup (f := g)))
      exact absurd hzero (ne_of_gt hpos)
  rw [h_essSup_eq]
  exact (ContinuousMap.enorm_eq_iSup_enorm f).symm

/--
[essSup_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma essSup_properties
  [MeasurableSpace α]
  {_μ : Measure α}
  [NormedAddCommGroup E] :
-- imply
  (∀ {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {E : Type*} [ENorm E] (f : α → E),
      ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ MeasureTheory.eLpNormEssSup f μ) ∧
    (∀ {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
      {μ : MeasureTheory.Measure α} [μ.IsOpenPosMeasure] {E : Type*} [SeminormedAddCommGroup E]
      (f : C(α, E)), MeasureTheory.eLpNormEssSup (fun x => f x) μ = ‖f‖ₑ) :=
-- proof
  ⟨fun {_} [_] {_} {_} [_] _ => ae_le_eLpNormEssSup,
    fun {_} [_] [_] [_] [_] {_} [_] {_} [_] f =>
      eLpNormEssSup_eq_enorm_continuousMap (f := f)⟩

/--
[holder_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma holder_integrable
  [MeasurableSpace α]
  {μ : Measure α}
  [NormedField 𝕜]
  {p q : ℝ≥0∞}
  {f g : α → 𝕜}
  [hpq : ENNReal.HolderConjugate p q]
-- given
  (hf : MemLp f p μ)
  (hg : MemLp g q μ) :
-- imply
  Integrable (f * g) μ :=
-- proof
  hf.integrable_mul hg

/--
[holder_eLpNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma holder_eLpNorm
  [MeasurableSpace α]
  {μ : Measure α}
  [NormedField 𝕜]
  {p q : ℝ≥0∞}
  {f g : α → 𝕜}
  [hpq : ENNReal.HolderConjugate p q]
-- given
  (hf : MemLp f p μ)
  (hg : MemLp g q μ) :
-- imply
  MeasureTheory.eLpNorm (f * g) 1 μ ≤ MeasureTheory.eLpNorm f p μ * MeasureTheory.eLpNorm g q μ := by
-- proof
  have h :=
    eLpNorm_smul_le_mul_eLpNorm (𝕜 := 𝕜) (E := 𝕜) (p := p) (q := q) (r := (1 : ℝ≥0∞))
      (φ := f) (f := g) hf.aestronglyMeasurable hg.aestronglyMeasurable
  simpa [smul_eq_mul] using h

/--
[holder_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma holder_inequality
  [MeasurableSpace α]
  {μ : Measure α}
  [NormedField 𝕜]
  {p q : ℝ≥0∞}
  {f g : α → 𝕜}
  [hpq : ENNReal.HolderConjugate p q]
-- given
  (hf : MemLp f p μ)
  (hg : MemLp g q μ) :
-- imply
  Integrable (f * g) μ ∧
    MeasureTheory.eLpNorm (f * g) 1 μ ≤ MeasureTheory.eLpNorm f p μ * MeasureTheory.eLpNorm g q μ :=
-- proof
  ⟨holder_integrable hf hg, holder_eLpNorm hf hg⟩

/--
[minkowski_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma minkowski_inequality
  [MeasurableSpace α]
  {μ : Measure α}
  [NormedAddCommGroup E]
  {p : ℝ≥0∞}
  {f g : α → E}
-- given
  (hp : 1 ≤ p)
  (_hf : AEStronglyMeasurable f μ)
  (_hg : AEStronglyMeasurable g μ) :
-- imply
  MeasureTheory.eLpNorm (f + g) p μ ≤ MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm g p μ :=
-- proof
  MeasureTheory.eLpNorm_add_le hp

/--
[riesz_fischer_Lp_completeSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma riesz_fischer_Lp_completeSpace
  [MeasurableSpace α]
  {μ : Measure α}
  [NormedAddCommGroup E]
  [CompleteSpace E]
  {p : ℝ≥0∞}
  [Fact (1 ≤ p)] :
-- imply
  CompleteSpace (MeasureTheory.Lp E p μ) :=
-- proof
  MeasureTheory.Lp.instCompleteSpace

/--
[lintegral_eq_iSup_lintegral_Icc_inter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma lintegral_eq_iSup_lintegral_Icc_inter
  {S : Set ℝ}
-- given
  (hS : MeasurableSet S)
  (g : ℝ → ℝ≥0∞)
  (hg : Measurable g) :
-- imply
  ∫⁻ x in S, g x ∂volume = ⨆ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, g x ∂volume := by
-- proof
  rw [← lintegral_indicator hS]
  have h_eq : ∀ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, g x ∂volume =
    ∫⁻ x, (Set.Icc (-(n : ℝ)) n ∩ S).indicator g x ∂volume :=
    fun n => (lintegral_indicator (measurableSet_Icc.inter hS) g).symm
  simp_rw [h_eq]
  set F : ℕ → ℝ → ℝ≥0∞ := fun n => (Set.Icc (-(n : ℝ)) n ∩ S).indicator g with hF_def
  have h_mono : Monotone F := by
    intro m n hmn x
    apply Set.indicator_le_indicator_of_subset
    · exact Set.inter_subset_inter
        (Set.Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn))
        (subset_rfl : S ⊆ S)
    · intro; exact bot_le
  have h_sup : (fun x => ⨆ n : ℕ, F n x) = S.indicator g := by
    ext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      apply le_antisymm
      · exact iSup_le (fun n => Set.indicator_le_self _ _ x)
      · obtain ⟨N, hN⟩ := exists_nat_ge |x|
        apply le_iSup_of_le N
        simp only [hF_def]
        rw [Set.indicator_of_mem (show x ∈ Set.Icc (-(N : ℝ)) N ∩ S from
          ⟨⟨neg_le_of_abs_le hN, le_of_abs_le hN⟩, hx⟩)]
    · rw [Set.indicator_of_notMem hx]
      apply le_antisymm
      · apply iSup_le; intro n
        simp only [hF_def]
        rw [Set.indicator_of_notMem (fun h => hx h.2)]
      · exact bot_le
  have h_meas : ∀ n : ℕ, Measurable (F n) :=
    fun n => hg.indicator (measurableSet_Icc.inter hS)
  rw [← h_sup, lintegral_iSup h_meas h_mono]

/--
[memLp_iff_iSup_lintegral_Icc_inter_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma memLp_iff_iSup_lintegral_Icc_inter_lt_top
  [NormedAddCommGroup F]
  [MeasurableSpace F]
  [BorelSpace F]
  [SecondCountableTopology F]
  {p : ℝ≥0∞}
  {S : Set ℝ}
  {f : ℝ → F}
-- given
  (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ⊤)
  (hS : MeasurableSet S)
  (hf : Measurable f) :
-- imply
  MemLp f p (volume.restrict S) ↔
    ⨆ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, (‖f x‖ₑ) ^ p.toReal ∂volume < ⊤ := by
-- proof
  have hf_aes : AEStronglyMeasurable f (volume.restrict S) := hf.aestronglyMeasurable.restrict
  constructor
  · intro hfp
    rw [← lintegral_eq_iSup_lintegral_Icc_inter hS _ (by measurability)]
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      hp_ne_zero hp_ne_top hf_aes).mp hfp
  · intro h
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top hf_aes]
    rwa [lintegral_eq_iSup_lintegral_Icc_inter hS _ (by measurability)]

/--
[memLp_of_polynomial_decay](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean)
-/
@[path]
lemma memLp_of_polynomial_decay
  [NormedAddCommGroup E]
  {f : ℝ → E}
  {C : ℝ}
  {q : ℝ}
  {p : ℝ≥0∞}
-- given
  (hf_meas : AEStronglyMeasurable f volume)
  (hC : 0 ≤ C)
  (hq : 1 < q)
  (hbound : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ (-q))
  (hp : 1 ≤ p) :
-- imply
  MemLp f p volume := by
-- proof
  by_cases hp_top : p = ⊤
  · subst hp_top
    apply memLp_top_of_bound hf_meas C
    filter_upwards with x
    calc ‖f x‖ ≤ C * (1 + |x|) ^ (-q) := hbound x
      _ ≤ C * 1 := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.rpow_le_one_of_one_le_of_nonpos
        · linarith [abs_nonneg x]
        · linarith
      _ = C := mul_one C
  · have hp_ne_zero : p ≠ 0 := by positivity
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hp_ge_one : (1 : ℝ) ≤ p.toReal := by
      have : (1 : ℝ≥0∞).toReal ≤ p.toReal :=
        (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
      simpa using this
    have hqp : (Module.finrank ℝ ℝ : ℝ) < q * p.toReal := by
      simp [Module.finrank_self]
      calc (1 : ℝ) < q := hq
        _ = q * 1 := (mul_one q).symm
        _ ≤ q * p.toReal := mul_le_mul_of_nonneg_left hp_ge_one (by linarith)
    have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(q * p.toReal))) volume :=
      integrable_one_add_norm hqp
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_top hf_meas]
    have hle : ∫⁻ (x : ℝ), ‖f x‖ₑ ^ p.toReal ∂volume ≤
        ∫⁻ (x : ℝ), ENNReal.ofReal (C ^ p.toReal * (1 + ‖x‖) ^ (-(q * p.toReal))) ∂volume := by
      refine lintegral_mono fun x => ?_
      rw [(ofReal_norm_eq_enorm (f x)).symm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
      apply ENNReal.ofReal_le_ofReal
      have hboundX : ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-q) := by
        have := hbound x
        rwa [show |x| = ‖x‖ from (Real.norm_eq_abs x).symm] at this
      calc ‖f x‖ ^ p.toReal
          ≤ (C * (1 + ‖x‖) ^ (-q)) ^ p.toReal :=
            Real.rpow_le_rpow (norm_nonneg _) hboundX hp_pos.le
        _ = C ^ p.toReal * ((1 + ‖x‖) ^ (-q)) ^ p.toReal :=
            Real.mul_rpow hC (Real.rpow_nonneg (by positivity) _)
        _ = C ^ p.toReal * (1 + ‖x‖) ^ (-(q * p.toReal)) := by
            congr 1
            rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖x‖)]
            ring_nf
    refine hle.trans_lt ?_
    simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
    rw [lintegral_const_mul _ (by measurability)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    rw [← lintegral_enorm_of_nonneg (fun x => Real.rpow_nonneg (by positivity) _)]
    exact hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral

-- created on 2026-10-23
-- updated on 2026-10-26
