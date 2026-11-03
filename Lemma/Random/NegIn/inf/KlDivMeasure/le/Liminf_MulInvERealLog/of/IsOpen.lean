import Lemma.Fin.GetMapSMul.eq.DivCountVec.of.Measurable
import Lemma.Random.Any_And_Any_And_InAndAll_InSMul.of.In.IsOpen
import Lemma.Random.IsProbabilityMeasure.of.Gt_0
import Lemma.Random.KlDiv.eq.All_EqGetMap0.of.Measurable
import Lemma.Random.Measurable.of.Gt_0
import Lemma.Random.SatisfiesLDP_MapPiFun_DivCountVec.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToRealGetMap.Measurable
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Polish
import Initialize.Tactic.Attr.Basic
open Classical ENNReal Filter Fin Finset InformationTheory MeasureTheory OrderDual Random Real
open scoped ENNReal


universe u


private lemma negInf {ι : Sort*} (f : ι → EReal) : -(⨅ i, f i) = ⨆ i, -f i := by
  apply (Equiv.injective toDual)
  rw [show toDual (-(⨅ i, f i)) = EReal.negOrderIso (⨅ i, f i) from rfl]
  rw [EReal.negOrderIso.map_iInf f]
  rw [show (⨅ i, EReal.negOrderIso (f i)) = ⨅ i, toDual (-f i) from rfl]
  rw [← toDual_iSup]

/--
On a Polish space, the empirical measures of i.i.d. samples obey the open-set lower bound in
Sanov's theorem. The speed is the sample size and the rate is the Kullback–Leibler divergence
from the common law.
-/
@[path]
private lemma main
  {α : Type u} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {U : Set (ProbabilityMeasure α)}
-- given
  (hU : IsOpen U) :
-- imply
  -(⨅ ν ∈ U, (klDiv (ν : Measure α) μ : EReal)) ≤
    liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
      ((@Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
        (fun ω => if hn : 0 < n then
          (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
            IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
        else μ.toProbabilityMeasure)
        (Measure.pi fun _ : Fin n => μ)) U)) atTop :=
-- proof
by
  let emp (n : ℕ) (ω : Fin n → α) : ProbabilityMeasure α :=
    if hn : 0 < n then
      (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
        IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
    else
      μ.toProbabilityMeasure
  let law (n : ℕ) : Measure (ProbabilityMeasure α) :=
    @Measure.map (Fin n → α) (ProbabilityMeasure α) _ _ (emp n)
      (Measure.pi fun _ : Fin n => μ)
  show -(⨅ ν ∈ U, (klDiv (ν : Measure α) μ : EReal)) ≤
    liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n U)) atTop
  have hneg : -(⨅ ν ∈ U, (klDiv (ν : Measure α) μ : EReal)) =
      ⨆ ν : ProbabilityMeasure α, ⨆ (_ : ν ∈ U), -(klDiv (ν : Measure α) μ : EReal) := by
    rw [negInf (fun ν => ⨅ (_ : ν ∈ U), (klDiv (ν : Measure α) μ : EReal))]
    refine iSup_congr fun ν => ?_
    exact negInf fun _ : ν ∈ U => (klDiv (ν : Measure α) μ : EReal)
  rw [hneg]
  refine iSup₂_le fun ν hν => ?_
  if htop : klDiv (ν : Measure α) μ = ⊤ then
    rw [htop, EReal.coe_ennreal_top, EReal.neg_top]
    exact bot_le
  else
    obtain ⟨β, βfin, βms, βsing, φ, hφ, V, hV, hνV, hmem⟩ :=
      Any_And_Any_And_InAndAll_InSMul.of.In.IsOpen hU hν
    let : Fintype β := βfin
    let : MeasurableSpace β := βms
    let : MeasurableSingletonClass β := βsing
    let I : (β → ℝ) → ENNReal := fun ξ =>
      if (∀ a, 0 ≤ ξ a) ∧ ∑ a, ξ a = 1 ∧ ∀ a, ((μ.map φ) {a}).toReal = 0 → ξ a = 0 then
        ENNReal.ofReal (∑ a, ξ a * log (ξ a / ((μ.map φ) {a}).toReal))
      else ⊤
    have hOn : ∀ ξ, (∀ a, 0 ≤ ξ a) → ∑ a, ξ a = 1 →
        (∀ a, ((μ.map φ) {a}).toReal = 0 → ξ a = 0) →
        I ξ = ENNReal.ofReal (∑ a, ξ a * log (ξ a / ((μ.map φ) {a}).toReal)) := by
      intro ξ hge hsum hvan
      simp only [I]
      rw [ite_eq_left ⟨hge, hsum, hvan⟩]
    have hOut : ∀ ξ, ¬((∀ a, 0 ≤ ξ a) ∧ ∑ a, ξ a = 1 ∧
        ∀ a, ((μ.map φ) {a}).toReal = 0 → ξ a = 0) → I ξ = ⊤ := by
      intro ξ hbad
      simp only [I]
      rw [ite_eq_right hbad]
    have hfinite :=
      SatisfiesLDP_MapPiFun_DivCountVec.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToRealGetMap.Measurable
        (α := β) (β := α) hφ hOn hOut
    have hlow := hfinite.lower_bound V hV
    have hcell : ∀ n (ω : Fin n → α),
        (fun a => (countVec (fun i => φ (ω i)) a : ℝ) / n) =
          fun a => ((((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i)).map φ) {a}).toReal := by
      intro n ω
      funext a
      rw [GetMapSMul.eq.DivCountVec.of.Measurable (n := n) (ω := ω) (φ := φ) (a := a) hφ,
        ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    have hpre : ∀ (n : ℕ), 0 < n →
        (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n) ⁻¹' V ⊆
          (emp n : (Fin n → α) → ProbabilityMeasure α) ⁻¹' U := by
      intro n hn ω hω
      have hmass :
        (fun a => ((((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i)).map φ) {a}).toReal) ∈ V := by
        simpa [hcell n ω] using hω
      have hemp : emp n ω ∈ U := by
        unfold emp
        exact dite_eq_left hn ▸ hmem hn ω hmass
      refine hemp
    have hfreqMeas : ∀ n, Measurable (fun ω : Fin n → α =>
        fun a => (countVec (fun i => φ (ω i)) a : ℝ) / n) := by
      intro n
      refine Measurable.of_eval fun a => ?_
      refine Measurable.div_const ?_ _
      have hcount : (fun ω : Fin n → α => (countVec (fun i => φ (ω i)) a : ℝ)) =
          fun ω => ∑ i, if φ (ω i) = a then (1 : ℝ) else 0 := by
        funext ω
        simp only [countVec]
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        if h : φ (ω i) = a then
          simp [h]
        else
          simp [h]
      rw [hcount]
      refine Finset.measurable_fun_sum Finset.univ fun i _ => ?_
      refine Measurable.ite ?_ measurable_const measurable_const
      have : {ω : Fin n → α | φ (ω i) = a} = (fun ω => ω i) ⁻¹' (φ ⁻¹' {a}) := rfl
      rw [this]
      exact (measurable_pi_apply i) (hφ (measurableSet_singleton a))
    have hempMeas : ∀ n, Measurable (emp n) := by
      intro n
      if hn : 0 < n then
        let rhs : (Fin n → α) → ProbabilityMeasure α :=
          fun ω => (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
            IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
        have heq : emp n = rhs := by
          funext ω
          unfold emp
          exact dite_eq_left hn
        refine heq.symm ▸ Measurable.of.Gt_0 (α := α) hn
      else
        let rhs : (Fin n → α) → ProbabilityMeasure α := fun _ => μ.toProbabilityMeasure
        have heq : emp n = rhs := by
          funext ω
          unfold emp
          exact dite_eq_right hn
        refine heq.symm ▸ measurable_const
    have hineq : ∀ (n : ℕ), 0 < n →
        ((Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n)) V ≤
          law n U := by
      intro n hn
      have hVm : MeasurableSet V := hV.measurableSet
      rw [Measure.map_apply (hfreqMeas n) hVm]
      exact (measure_mono (hpre n hn)).trans (Measure.le_map_apply (hempMeas n).aemeasurable U)
    have hterm : ∀ᶠ n in atTop,
        ((n : ℕ) : EReal)⁻¹ * ENNReal.log
          (((Measure.pi fun _ : Fin n => μ).map
            (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n)) V) ≤
        ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n U) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      refine mul_le_mul_of_nonneg_left (ENNReal.log_le_log (hineq n hn)) ?_
      exact EReal.inv_nonneg_of_nonneg (by exact_mod_cast (Nat.zero_le n))
    have hlim : liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
        (((Measure.pi fun _ : Fin n => μ).map
          (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n)) V)) atTop ≤
        liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n U)) atTop :=
      liminf_le_liminf hterm
    let p : β → ℝ := fun a => ((ν : Measure α).map φ {a}).toReal
    have hpV : p ∈ V := hνV
    have hsplit := (klDiv_ne_top_iff (μ := (ν : Measure α)) (ν := μ)).mp htop
    have hmapac : (ν : Measure α).map φ ≪ μ.map φ := hsplit.1.map hφ
    have hge : ∀ a, 0 ≤ p a := fun _ => ENNReal.toReal_nonneg
    have hprob : IsProbabilityMeasure ((ν : Measure α).map φ) :=
      (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
    have hsum : ∑ a, p a = 1 := by
      have hsing : ∑ a, ((ν : Measure α).map φ).real {a} =
          ((ν : Measure α).map φ).real Set.univ := by
        rw [← Finset.coe_univ]
        exact sum_measureReal_singleton (μ := (ν : Measure α).map φ) Finset.univ
      calc ∑ a, p a
        _ = ∑ a, ((ν : Measure α).map φ).real {a} := by simp [p, measureReal_def]
        _ = ((ν : Measure α).map φ).real Set.univ := hsing
        _ = 1 := probReal_univ
    have hvan : ∀ a, ((μ.map φ) {a}).toReal = 0 → p a = 0 := by
      intro a ha
      have hμ0 : (μ.map φ) {a} = 0 := by
        obtain h0 | hinf := (ENNReal.toReal_eq_zero_iff ((μ.map φ) {a})).1 ha
        · exact h0
        · exact absurd hinf (measure_ne_top _ _)
      have hν0 : ((ν : Measure α).map φ) {a} = 0 := hmapac hμ0
      simp [p, hν0]
    have hIp : I p = klDiv ((ν : Measure α).map φ) (μ.map φ) := by
      have hkl := KlDiv.eq.All_EqGetMap0.of.Measurable (μ := μ) (ν := (ν : Measure α)) hφ
      rw [hkl, ite_eq_left (fun a h0 => hmapac h0)]
      simp only [I]
      rw [ite_eq_left ⟨hge, hsum, hvan⟩]
    have hle : klDiv ((ν : Measure α).map φ) (μ.map φ) ≤ klDiv (ν : Measure α) μ :=
      klDiv_map_le (ν : Measure α) μ hφ
    have hcoe : (I p : EReal) ≤ (klDiv (ν : Measure α) μ : EReal) := by
      rw [hIp]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hle
    have hinf : (⨅ x ∈ V, (I x : EReal)) ≤ (I p : EReal) := iInf₂_le p hpV
    have hnegI : -(klDiv (ν : Measure α) μ : EReal) ≤ -(⨅ x ∈ V, (I x : EReal)) := by
      calc -(klDiv (ν : Measure α) μ : EReal)
        _ ≤ -(I p : EReal) := (EReal.neg_le_neg_iff).mpr hcoe
        _ ≤ -(⨅ x ∈ V, (I x : EReal)) := (EReal.neg_le_neg_iff).mpr hinf
    exact hnegI.trans (hlow.trans hlim)


-- created on 2026-11-02
