import Mathlib.Basic.ENNReal.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Semicontinuity.Basic
import Lemma.ENNReal.SatisfiesLDP_Map_DivCountVecPi_ToMeasure.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0
import Initialize.Tactic.Attr.Basic
open Classical ENNReal MeasureTheory Real


private lemma satisfiesLDP [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {μ : PMF α} {I : (α → ℝ) → ENNReal} (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → (∀ a, (μ a).toReal = 0 → ν a = 0) → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (μ a).toReal))) (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ∀ a, (μ a).toReal = 0 → ν a = 0) → I ν = ⊤) :
  SatisfiesLDP (fun n => Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure)) I := by
  let α₀ := Subtype (fun a : α => 0 < (μ a).toReal)
  have hnull : ∀ a, ¬ 0 < (μ a).toReal → μ a = 0 := by
    intro a ha
    have hnot : ¬ (0 < μ a ∧ μ a < ⊤) := (not_congr ENNReal.toReal_pos_iff).mp ha
    simp only [not_and_or, not_lt] at hnot
    obtain h0 | htop := hnot
    · exact le_antisymm h0 bot_le
    · exact absurd (lt_of_le_of_lt (μ.coe_le_one a) one_lt_top) (not_lt_of_ge htop)
  have hμsum : ∑ a, μ a = 1 := by
    have htsum : ∑' a, μ a = 1 := μ.tsum_coe
    rwa [tsum_fintype (L := SummationFilter.unconditional α)] at htsum
  have hpossum : ∑ b : α₀, μ b.val = 1 := by
    have hcompl : ∑ b : Subtype (fun a => ¬ 0 < (μ a).toReal), μ b.val = 0 := by
      refine Finset.sum_eq_zero fun b _ => hnull b.val b.prop
    have hadd := Fintype.sum_subtype_add_sum_subtype (fun a => 0 < (μ a).toReal) (fun a => μ a)
    rw [hcompl, add_zero] at hadd
    exact hadd.trans hμsum
  let μ₀ : PMF α₀ := PMF.ofFintype (fun b => μ b.val) hpossum
  let extend : (α₀ → ℝ) → α → ℝ := fun ρ a => if h : 0 < (μ a).toReal then ρ ⟨a, h⟩ else 0
  have hsumext (ρ : α₀ → ℝ) : ∑ a, extend ρ a = ∑ b, ρ b := by
    have hcompl : ∑ b : Subtype (fun a => ¬ 0 < (μ a).toReal), extend ρ b.val = 0 := by
      refine Finset.sum_eq_zero fun b _ => by simp [extend, b.prop]
    have hadd := Fintype.sum_subtype_add_sum_subtype (fun a => 0 < (μ a).toReal) (extend ρ)
    have hpos : ∑ b : α₀, extend ρ b.val = ∑ b, ρ b := by
      refine Finset.sum_congr rfl fun b _ => by simp [extend, b.prop]
    rw [hcompl, add_zero, hpos] at hadd
    simpa using hadd.symm
  let I₀ : (α₀ → ℝ) → ENNReal := fun ρ => I (extend ρ)
  have hpos : ∀ b, 0 < (μ₀ b).toReal := by
    intro b
    simpa [μ₀, PMF.ofFintype_apply] using b.prop
  have hOn' : ∀ ρ, (∀ b, 0 ≤ ρ b) → ∑ b, ρ b = 1 → I₀ ρ = ENNReal.ofReal (∑ b, ρ b * log (ρ b / (μ₀ b).toReal)) := by
    intro ρ hge hsumρ
    have hgeα : ∀ a, 0 ≤ extend ρ a := by
      intro a
      if h : 0 < (μ a).toReal then
        simpa [extend, h] using hge ⟨a, h⟩
      else
        simp [extend, h]
    have hvan : ∀ a, (μ a).toReal = 0 → extend ρ a = 0 := by
      intro a ha
      have : ¬ 0 < (μ a).toReal := by linarith [ha]
      simp [extend, this]
    rw [show I₀ ρ = I (extend ρ) from rfl, hOn (extend ρ) hgeα (by rw [hsumext ρ, hsumρ]) hvan]
    congr 1
    have hKLcompl : ∑ b : Subtype (fun a => ¬ 0 < (μ a).toReal), extend ρ b.val * log (extend ρ b.val / (μ b.val).toReal) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      have h0 : (μ b.val).toReal = 0 := le_antisymm (not_lt.mp b.prop) ENNReal.toReal_nonneg
      rw [show extend ρ b.val = 0 by simp [extend, b.prop], h0, _root_.div_zero, Real.log_zero, mul_zero]
    have hKLpos : ∑ b : α₀, extend ρ b.val * log (extend ρ b.val / (μ b.val).toReal) = ∑ b, ρ b * log (ρ b / (μ b.val).toReal) := by
      refine Finset.sum_congr rfl fun b _ => by simp [extend, b.prop]
    have hadd := Fintype.sum_subtype_add_sum_subtype (fun a => 0 < (μ a).toReal) (fun a => extend ρ a * log (extend ρ a / (μ a).toReal))
    rw [hKLcompl, add_zero] at hadd
    rw [← hadd, hKLpos]
    simp [μ₀, PMF.ofFintype_apply]
  have hOut' : ∀ ρ, ¬((∀ b, 0 ≤ ρ b) ∧ ∑ b, ρ b = 1) → I₀ ρ = ⊤ := by
    intro ρ hbad
    have hvan : ∀ a, (μ a).toReal = 0 → extend ρ a = 0 := by
      intro a ha
      have : ¬ 0 < (μ a).toReal := by linarith [ha]
      simp [extend, this]
    have hbad' : ¬((∀ a, 0 ≤ extend ρ a) ∧ ∑ a, extend ρ a = 1 ∧ ∀ a, (μ a).toReal = 0 → extend ρ a = 0) := by
      intro h
      apply hbad
      refine ⟨fun b => ?_, ?_⟩
      · simpa [extend, b.prop] using h.1 b.val
      · rw [← hsumext ρ, h.2.1]
    rw [show I₀ ρ = I (extend ρ) from rfl, hOut (extend ρ) hbad']
  have hfinite := SatisfiesLDP_Map_DivCountVecPi_ToMeasure.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0 hpos hOn' hOut'
  have hcont : Continuous extend := by
    refine continuous_pi fun a => ?_
    if h : 0 < (μ a).toReal then
      simpa [extend, h] using (continuous_apply (⟨a, h⟩ : α₀))
    else
      simpa [extend, h] using continuous_const
  have hfreq : ∀ {n : ℕ} (η : Fin n → α₀), (fun a => (countVec (fun i => (η i).val) a : ℝ) / n) = extend (fun b => (countVec η b : ℝ) / n) := by
    intro n η
    funext a
    if h : 0 < (μ a).toReal then
      have hcount : countVec (fun i => (η i).val) a = countVec η ⟨a, h⟩ := by
        simp only [countVec]
        refine Finset.sum_congr rfl fun i _ => ?_
        if hi : (η i).val = a then
          simp [show η i = ⟨a, h⟩ from Subtype.ext hi]
        else
          have hne : η i ≠ ⟨a, h⟩ := by
            intro heq
            exact hi (by simp [heq])
          simp [hi, hne]
      simp [extend, h, hcount]
    else
      have hcount : countVec (fun i => (η i).val) a = 0 := by
        simp only [countVec]
        refine Finset.sum_eq_zero fun i _ => ?_
        have : (η i).val ≠ a := by
          intro heq
          exact h (by simpa [heq] using (η i).prop)
        simp [this]
      simp [extend, h, hcount]
  have hpush : ∀ n, (Measure.pi fun _ : Fin n => μ₀.toMeasure).map (fun η i => (η i).val) = Measure.pi fun _ : Fin n => μ.toMeasure := by
    intro n
    refine Measure.ext fun s _ => ?_
    let t : Finset (Fin n → α) := Finset.univ.filter (fun ω => ω ∈ s)
    have hsplit : ∀ ν : Measure (Fin n → α), ν s = ∑ ω ∈ t, ν {ω} := by
      intro ν
      have hunion : s = ⋃ ω ∈ t, ({ω} : Set (Fin n → α)) := by
        ext ω
        simp [t]
      rw [hunion, measure_biUnion_finset]
      ·
        intro ω _ ω' _ hne
        simpa [Function.onFun] using Set.disjoint_singleton.mpr hne
      ·
        intro ω _
        exact measurableSet_singleton ω
    rw [hsplit ((Measure.pi fun _ : Fin n => μ₀.toMeasure).map (fun η i => (η i).val)), hsplit (Measure.pi fun _ : Fin n => μ.toMeasure)]
    refine Finset.sum_congr rfl fun ω _ => ?_
    if hω : ∀ i, 0 < (μ (ω i)).toReal then
      let η : Fin n → α₀ := fun i => ⟨ω i, hω i⟩
      have hpre : (fun ζ : Fin n → α₀ => fun i => (ζ i).val) ⁻¹' {ω} = {η} := by
        ext ζ
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        ·
          intro heq
          funext i
          exact Subtype.ext (congr_fun heq i)
        ·
          intro heq
          rw [heq]
      rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton ω), hpre, Measure.pi_singleton, Measure.pi_singleton]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [μ₀.toMeasure_apply_singleton (η i) (measurableSet_singleton _), μ.toMeasure_apply_singleton (ω i) (measurableSet_singleton _)]
      simp [μ₀, η, PMF.ofFintype_apply]
    else
      simp only [not_forall] at hω
      obtain ⟨i, hi⟩ := hω
      have hempty : (fun ζ : Fin n → α₀ => fun j => (ζ j).val) ⁻¹' {ω} = ∅ := by
        ext ζ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro heq
        exact hi (by simpa [congr_fun heq i] using (ζ i).prop)
      rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton ω), hempty, measure_empty, Measure.pi_singleton]
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ((μ.toMeasure_apply_singleton (ω i) (measurableSet_singleton _)).trans (hnull (ω i) hi))).symm
  have hlaw : ∀ n, Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure) = Measure.map extend (Measure.map (fun η : Fin n → α₀ => fun b => (countVec η b : ℝ) / n) (Measure.pi fun _ : Fin n => μ₀.toMeasure)) := by
    intro n
    have hcomp : (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) ∘ (fun η i => (η i).val) = extend ∘ (fun η : Fin n → α₀ => fun b => (countVec η b : ℝ) / n) := by
      funext η
      exact hfreq η
    rw [← hpush n, Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hcomp, ← Measure.map_map hcont.measurable (measurable_of_finite _)]
  have hinf : ∀ U : Set (α → ℝ), (⨅ ν ∈ U, (I ν : EReal)) = (⨅ ρ ∈ extend ⁻¹' U, (I₀ ρ : EReal)) := by
    intro U
    apply le_antisymm
    ·
      refine le_iInf₂ fun ρ hρ => ?_
      exact iInf₂_le (extend ρ) hρ
    ·
      refine le_iInf₂ fun ν hν => ?_
      if hgood : (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ∀ a, (μ a).toReal = 0 → ν a = 0 then
        let ρ : α₀ → ℝ := fun b => ν b.val
        have hext : extend ρ = ν := by
          funext a
          if h : 0 < (μ a).toReal then
            simp [extend, ρ, h]
          else
            have hz : (μ a).toReal = 0 := le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
            simp [extend, ρ, h, hgood.2.2 a hz]
        have hρ : ρ ∈ extend ⁻¹' U := by
          simpa [hext] using hν
        rw [show (I ν : EReal) = I₀ ρ by simp [I₀, hext]]
        refine iInf₂_le ρ hρ
      else
        rw [hOut ν hgood, EReal.coe_ennreal_top]
        apply le_top
  have hsc : LowerSemicontinuous I := by
    have hI₀ : LowerSemicontinuous I₀ := hfinite.isRateFunction.lowerSemicontinuous
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    obtain rfl | hy := eq_or_ne y ⊤
    ·
      have : I ⁻¹' Set.Iic ⊤ = Set.univ := by
        ext ν
        simp
      exact this ▸ isClosed_univ
    ·
      let V : Set (α → ℝ) := {ν | ∀ a, (μ a).toReal = 0 → ν a = 0}
      let restr : (α → ℝ) → α₀ → ℝ := fun ν b => ν b.val
      have hS : IsClosed (I₀ ⁻¹' Set.Iic y) := hI₀.isClosed_preimage y
      have hV : IsClosed V := by
        have : V = ⋂ a, {ν | (μ a).toReal = 0 → ν a = 0} := by
          ext ν
          simp [V]
        rw [this]
        refine isClosed_iInter fun a => ?_
        if h : (μ a).toReal = 0 then
          simpa [h] using isClosed_eq (continuous_apply a) continuous_const
        else
          have : {ν : α → ℝ | (μ a).toReal = 0 → ν a = 0} = Set.univ := by
            ext ν
            simp [h]
          exact this ▸ isClosed_univ
      have hset : I ⁻¹' Set.Iic y = V ∩ restr ⁻¹' (I₀ ⁻¹' Set.Iic y) := by
        ext ν
        constructor
        ·
          intro hle
          rw [Set.mem_preimage, Set.mem_Iic] at hle
          have hne : I ν ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hle ((lt_top_iff_ne_top).mpr hy))
          have hgood : (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ∀ a, (μ a).toReal = 0 → ν a = 0 := by
            by_contra hbad
            exact hne (hOut ν hbad)
          refine ⟨fun a ha => hgood.2.2 a ha, ?_⟩
          have hext : extend (restr ν) = ν := by
            funext a
            if h : 0 < (μ a).toReal then
              simp [extend, restr, h]
            else
              have hz : (μ a).toReal = 0 := le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
              simp [extend, restr, h, hgood.2.2 a hz]
          simpa [I₀, hext, Set.mem_preimage] using hle
        ·
          intro h
          have hext : extend (restr ν) = ν := by
            funext a
            if hpos : 0 < (μ a).toReal then
              simp [extend, restr, hpos]
            else
              have hz : (μ a).toReal = 0 := le_antisymm (not_lt.mp hpos) ENNReal.toReal_nonneg
              simp [extend, restr, hpos, h.1 a hz]
          simpa [I₀, hext] using h.2
      simpa [hset] using hV.inter (hS.preimage (continuous_pi fun b => continuous_apply b.val))
  refine ⟨⟨hsc⟩, ?_, ?_⟩
  ·
    intro U hU
    rw [hinf U]
    have hpre : IsOpen (extend ⁻¹' U) := hU.preimage hcont
    have hfun : (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure)) U)) = (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((Measure.map (fun η : Fin n → α₀ => fun b => (countVec η b : ℝ) / n) (Measure.pi fun _ : Fin n => μ₀.toMeasure)) (extend ⁻¹' U))) := by
      ext n
      rw [hlaw n, Measure.map_apply hcont.measurable hU.measurableSet]
    simpa [hfun] using hfinite.lower_bound (extend ⁻¹' U) hpre
  ·
    intro F hF
    rw [hinf F]
    have hpre : IsClosed (extend ⁻¹' F) := hF.preimage hcont
    have hfun : (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure)) F)) = (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((Measure.map (fun η : Fin n → α₀ => fun b => (countVec η b : ℝ) / n) (Measure.pi fun _ : Fin n => μ₀.toMeasure)) (extend ⁻¹' F))) := by
      ext n
      rw [hlaw n, Measure.map_apply hcont.measurable hF.measurableSet]
    simpa [hfun] using hfinite.upper_bound (extend ⁻¹' F) hpre

/--
On a finite alphabet, the empirical frequency satisfies a large deviation principle of speed `n` even
when some reference masses vanish. The rate is the usual relative entropy on probability vectors
supported on the positive atoms, and `⊤` when a vector charges a null atom or leaves the simplex.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : PMF α}
  {I : (α → ℝ) → ENNReal}
-- given
  (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → (∀ a, (μ a).toReal = 0 → ν a = 0) → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (μ a).toReal)))
  (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ∀ a, (μ a).toReal = 0 → ν a = 0) → I ν = ⊤) :
-- imply
  SatisfiesLDP (fun n => Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure)) I :=
-- proof
  satisfiesLDP hOn hOut


-- created on 2026-11-02
