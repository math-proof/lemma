import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.EReal.Inv
import Lemma.Fin.Pi_ToMeasure.of.EqSum
import Lemma.Finset.AbsAddMulInvLogInf'.le.DivMulCardAddAddLogDivLog2'1.of.All_GtToReal_0.Nonempty.All_EqSum.Gt_0
import Initialize.Tactic.Attr.Basic
open Asymptotics Filter Fin Finset MeasureTheory Real


private lemma sum_countVec [Fintype α] [DecidableEq α] {n : ℕ} (ω : Fin n → α) :
  ∑ a, countVec ω a = n := by
  simp only [countVec]
  rw [Finset.sum_comm]
  have hinner : ∀ i, ∑ a, (if ω i = a then 1 else 0) = 1 := by
    intro i
    simp [eq_comm]
  simp [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

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

private lemma tendsto_err [Fintype α] :
  Tendsto (fun n : ℕ => (Fintype.card α : ℝ) * (log ((n : ℝ) + 1) + log (n : ℝ) / 2 + 1) / n) atTop (nhds 0) := by
  have hexp :=
    (tendsto_log_succ_div.add ((tendsto_log_div.const_mul (1 / 2)).add tendsto_one_div_atTop_nhds_zero_nat)).const_mul
      (Fintype.card α : ℝ)
  refine Tendsto.congr' ?_ (by simpa using hexp)
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp [Nat.cast_ne_zero.mpr hn]
  ring

private lemma rate_le [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ} {μ : PMF α} {A : Set (α → ℝ)} (hn : 0 < n) (hμ : ∀ a, 0 < (μ a).toReal) :
  ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ A}) ≤
    toEReal ((Fintype.card α : ℝ) * (log ((n : ℝ) + 1) + log (n : ℝ) / 2 + 1) / n) + (-⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ A}, toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) := by
  classical
  let base : Finset (α → ℕ) :=
    ((univ : Finset (α → Fin (n + 1))).filter (fun c => ∑ a, (c a).1 = n)).image (fun c a => (c a).1)
  let s := base.filter (fun c => (fun a => (c a : ℝ) / n) ∈ A)
  let kl (c : α → ℕ) : ℝ := ∑ a, ((c a : ℝ) / n) * log (((c a : ℝ) / n) / (μ a).toReal)
  let simplex := {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ A}
  have hs : ∀ c ∈ s, ∑ a, c a = n := by
    intro c hc
    obtain ⟨hbase, _⟩ := mem_filter.mp hc
    obtain ⟨c0, hc0, rfl⟩ := mem_image.mp hbase
    simpa using (mem_filter.mp hc0).2
  have hset : {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ A} =
      ⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α)) := by
    ext ω
    constructor
    ·
      intro hmem
      have hsum := sum_countVec ω
      have hle : ∀ a, countVec ω a < n + 1 := by
        intro a
        have hsing := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a) (f := countVec ω)
        omega
      refine Set.mem_iUnion₂.mpr ⟨countVec ω, ?_, ?_⟩
      ·
        refine mem_filter.mpr ⟨?_, hmem⟩
        refine mem_image.mpr ⟨fun a => ⟨countVec ω a, hle a⟩, ?_, rfl⟩
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        simp [hsum]
      · simp [empiricalSet]
    ·
      intro hmem
      obtain ⟨c, hc, hω⟩ := Set.mem_iUnion₂.mp hmem
      have hcount : ∀ a, countVec ω a = c a := by
        simpa [empiricalSet, mem_coe, mem_filter, mem_univ, true_and] using hω
      simpa [hcount] using (mem_filter.mp hc).2
  obtain hempty | hne := s.eq_empty_or_nonempty
  ·
    have hemptyUnion : (⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α))) = ∅ := by
      simp [hempty]
    rw [hset, hemptyUnion, measure_empty, ENNReal.log_zero]
    have hninv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
    have hmul : (((n : ℝ) : EReal)⁻¹) * ⊥ =
      if 0 < (n : ℝ)⁻¹ then ⊥ else if (n : ℝ)⁻¹ = 0 then 0 else ⊤ := rfl
    rw [← EReal.coe_coe_eq_natCast n, hmul, ite_eq_left hninv]
    apply bot_le
  ·
    have hμs : ∀ c ∈ s, ∀ a, 0 < c a → 0 < (μ a).toReal := fun _ _ _ _ => hμ _
    have habs :=
      AbsAddMulInvLogInf'.le.DivMulCardAddAddLogDivLog2'1.of.All_GtToReal_0.Nonempty.All_EqSum.Gt_0
        hn hs hne hμs
    have hreal : ((n : ℝ)⁻¹) * log (((Measure.pi fun _ : Fin n => μ.toMeasure)
        (⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α)))).toReal) ≤
        (Fintype.card α : ℝ) * (log ((n : ℝ) + 1) + log (n : ℝ) / 2 + 1) / n - s.inf' hne kl := by
      rw [le_sub_iff_add_le]
      simpa [kl] using (abs_le.mp habs).2
    rw [hset]
    have hpos : 0 < (Measure.pi fun _ : Fin n => μ.toMeasure)
        (⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α))) := by
      obtain ⟨c, hc⟩ := hne
      have hmass : 0 < (Nat.multinomial univ c : ENNReal) * ∏ a, μ a ^ c a := by
        refine ENNReal.mul_pos ?_ ?_
        · exact_mod_cast (Nat.multinomial_pos univ c).ne'
        ·
          refine Finset.prod_ne_zero_iff.mpr ?_
          intro a _
          exact pow_ne_zero _ ((ENNReal.toReal_pos_iff.mp (hμ a)).1).ne'
      have hsub : {ω : Fin n → α | ∀ a, countVec ω a = c a} ⊆ ⋃ d ∈ s, (empiricalSet n d : Set (Fin n → α)) := by
        intro ω hω
        refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
        simpa [empiricalSet] using hω
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rwa [Pi_ToMeasure.of.EqSum (hs c hc) μ]
    have hneTop : (Measure.pi fun _ : Fin n => μ.toMeasure)
        (⋃ c ∈ s, (empiricalSet n c : Set (Fin n → α))) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      refine le_trans (measure_mono (Set.subset_univ _)) ?_
      rw [Measure.pi_univ]
      simp
    rw [ENNReal.log_pos_real hpos.ne' hneTop]
    have hinv : ((n : EReal)⁻¹) = toEReal ((n : ℝ)⁻¹) := by
      rw [← EReal.coe_coe_eq_natCast n]
      exact (EReal.coe_inv (n : ℝ)).symm
    rw [hinv, ← EReal.coe_mul]
    refine (EReal.coe_le_coe_iff.mpr hreal).trans ?_
    have hmin := exists_mem_eq_inf' hne kl
    obtain ⟨cMin, hcMin, hklMin⟩ := hmin
    have hfreq : (fun a => (cMin a : ℝ) / n) ∈ simplex := by
      refine ⟨?_, ?_, (mem_filter.mp hcMin).2⟩
      ·
        intro a
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      ·
        have hsumc : ∑ a, cMin a = n := hs cMin hcMin
        change ∑ a, (cMin a : ℝ) / n = 1
        rw [← Finset.sum_div, ← Nat.cast_sum, hsumc, div_self (Nat.cast_ne_zero.mpr hn.ne')]
    have hklle : ⨅ ν ∈ simplex, toEReal (∑ a, ν a * log (ν a / (μ a).toReal)) ≤
        toEReal (s.inf' hne kl) := by
      rw [hklMin]
      simp only [kl]
      exact iInf₂_le (f := fun ν (_ : ν ∈ simplex) => toEReal (∑ a, ν a * log (ν a / (μ a).toReal)))
        (fun a => (cMin a : ℝ) / n) hfreq
    have hneg : -toEReal (s.inf' hne kl) ≤
        -(⨅ ν ∈ simplex, toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) :=
      EReal.neg_le_neg_iff.mpr hklle
    have hsub : toEReal ((Fintype.card α : ℝ) * (log ((n : ℝ) + 1) + log (n : ℝ) / 2 + 1) / n -
        s.inf' hne kl) =
        toEReal ((Fintype.card α : ℝ) * (log ((n : ℝ) + 1) + log (n : ℝ) / 2 + 1) / n) +
          -toEReal (s.inf' hne kl) := by
      rw [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg]
    rw [hsub]
    exact add_le_add_right hneg _

private lemma limsup_le [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {μ : PMF α} {A : Set (α → ℝ)} (hμ : ∀ a, 0 < (μ a).toReal) :
  limsup (fun n : ℕ => ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ A})) atTop ≤
    -(⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ A}, toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) := by
  let rate (n : ℕ) : EReal := ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure)
    {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ A})
  let err (n : ℕ) : ℝ := (Fintype.card α : ℝ) * (log ((n : ℝ) + 1) + log (n : ℝ) / 2 + 1) / n
  generalize hkl : (⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ A},
    toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) = k
  cases k with
  | bot =>
    exact le_top
  | top =>
    rw [limsup_eq]
    refine sInf_le ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hle := rate_le (μ := μ) (A := A) hn hμ
    rw [hkl, EReal.neg_top, EReal.add_bot] at hle
    simpa [rate] using hle
  | coe r =>
    have hle : ∀ᶠ n : ℕ in atTop, rate n ≤ toEReal (err n) + (-(r : EReal)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hr := rate_le (μ := μ) (A := A) hn hμ
      rw [hkl] at hr
      simpa [rate, err] using hr
    have herr : Tendsto (fun n : ℕ => toEReal (err n) + (-(r : EReal))) atTop (nhds (-(r : EReal))) := by
      have hreal : Tendsto (fun n : ℕ => err n + (-r)) atTop (nhds (-r)) := by
        simpa using (tendsto_err (α := α)).add (tendsto_const_nhds (x := -r))
      refine Tendsto.congr (fun n => ?_) (EReal.tendsto_coe.mpr hreal)
      rw [EReal.coe_add, EReal.coe_neg]
    have hlimg : limsup (fun n : ℕ => toEReal (err n) + (-(r : EReal))) atTop = -(r : EReal) :=
      herr.limsup_eq
    rw [← hlimg, limsup_eq, limsup_eq]
    refine sInf_le_sInf ?_
    intro a ha
    filter_upwards [ha, hle] with n hn hrate
    simpa [rate, err] using hrate.trans hn

/--
If every reference mass is positive, the logarithmic probability that the empirical frequency
lands in a set `A` has limsup at most the negative infimum of `KL(ν ‖ μ)` over the probability
vectors in `A`. An empty event contributes `-∞`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : PMF α} {A : Set (α → ℝ)}
-- given
  (hμ : ∀ a, 0 < (μ a).toReal) :
-- imply
  limsup (fun n : ℕ => ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ A})) atTop ≤
    -(⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ A}, toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) :=
-- proof
  limsup_le hμ


-- created on 2026-11-02
