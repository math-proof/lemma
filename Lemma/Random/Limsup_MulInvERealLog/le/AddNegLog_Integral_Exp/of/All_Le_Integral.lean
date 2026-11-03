import Lemma.Random.GetPiFunSetOfGeSum_Mul.le.OfRealMulExpMulNegPowIntegral_Exp.of.BoundedContinuousFunction
import Lemma.Random.IsProbabilityMeasure.of.Gt_0
import Lemma.Random.Measurable.of.Gt_0
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Initialize.Tactic.Attr.Basic
open ENNReal Filter MeasureTheory Random Real
open scoped ENNReal


private lemma integral_emp [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] {n : ℕ} (ω : Fin n → α) (f : BoundedContinuousFunction α ℝ) : ∫ x, f x ∂((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i)) = (∑ i, f (ω i)) / n := by
  have hf : StronglyMeasurable (⇑f) := f.continuous.stronglyMeasurable
  rw [integral_smul_measure]
  have hint : ∀ i ∈ Finset.univ, Integrable (⇑f) (Measure.dirac (ω i)) :=
    fun _ _ => integrable_dirac' hf (by finiteness)
  rw [integral_finsetSum_measure hint]
  have hsum : ∑ i, ∫ x, f x ∂Measure.dirac (ω i) = ∑ i, f (ω i) := by
    refine Finset.sum_congr rfl fun i _ => integral_dirac' (⇑f) (ω i) hf
  rw [hsum, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul]

private lemma measurable_integral [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] (f : BoundedContinuousFunction α ℝ) : Measurable (fun ν : ProbabilityMeasure α => ∫ x, f x ∂(ν : Measure α)) := by
  have heq : (fun ν : ProbabilityMeasure α => ∫ x, f x ∂(ν : Measure α)) =
      fun ν : ProbabilityMeasure α => (∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure α)).toReal -
        (∫⁻ x, ENNReal.ofReal (-f x) ∂(ν : Measure α)).toReal := by
    funext ν
    have hint : Integrable (⇑f) (ν : Measure α) := by
      refine ⟨f.continuous.aestronglyMeasurable, ?_⟩
      refine HasFiniteIntegral.of_bounded (C := ‖f‖) (ae_of_all _ fun x => f.norm_coe_le_norm x)
    refine integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  rw [heq]
  refine Measurable.sub ?_ ?_
  · exact measurable_toReal.comp ((Measure.measurable_lintegral (measurable_ofReal.comp f.continuous.measurable)).comp measurable_subtype_coe)
  · exact measurable_toReal.comp ((Measure.measurable_lintegral (measurable_ofReal.comp f.continuous.neg.measurable)).comp measurable_subtype_coe)

/--
Chernoff's bound for the empirical measure of an i.i.d. sample. If every measure in `F` integrates
a bounded continuous function above `c`, the logarithmic probability of the empirical measure
landing in `F` is at most `c` below the logarithmic moment generating function.
-/
@[path]
private lemma main
  [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {F : Set (ProbabilityMeasure α)}
  {f : BoundedContinuousFunction α ℝ}
  {c : ℝ}
-- given
  (hF : ∀ ν ∈ F, c ≤ ∫ x, f x ∂(ν : Measure α)) :
-- imply
  limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
    ((@Measure.map (Fin n → α) (ProbabilityMeasure α) _ _
      (fun ω => if hn : 0 < n then
        (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
          IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)
      else μ.toProbabilityMeasure)
      (Measure.pi fun _ : Fin n => μ)) F)) atTop ≤
    ((-c + log (∫ x, exp (f x) ∂μ) : ℝ) : EReal) :=
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
  show limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (law n F)) atTop ≤
    ((-c + log (∫ x, exp (f x) ∂μ) : ℝ) : EReal)
  let G : Set (ProbabilityMeasure α) := {ν | c ≤ ∫ x, f x ∂(ν : Measure α)}
  have hGmeas : MeasurableSet G := by
    have : G = (fun ν : ProbabilityMeasure α => ∫ x, f x ∂(ν : Measure α)) ⁻¹' Set.Ici c := by
      ext ν
      simp [G]
    rw [this]
    exact (measurable_integral f) measurableSet_Ici
  have hFG : F ⊆ G := fun ν hν => hF ν hν
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
  have hbound : ∀ n, 0 < n → law n F ≤
      ENNReal.ofReal (exp (-c * n) * (∫ x, exp (f x) ∂μ) ^ n) := by
    intro n hn
    have hmono : law n F ≤ law n G := measure_mono hFG
    refine hmono.trans ?_
    have hmap : law n G = (Measure.pi fun _ : Fin n => μ) ((emp n : (Fin n → α) → ProbabilityMeasure α) ⁻¹' G) := by
      simpa [law] using Measure.map_apply (hempMeas n) hGmeas
    rw [hmap]
    have hsub : (emp n : (Fin n → α) → ProbabilityMeasure α) ⁻¹' G ⊆
      {ω | c * n ≤ ∑ i, f (ω i)} := by
      intro ω hω
      have hint : c ≤ ∫ x, f x ∂((emp n ω : ProbabilityMeasure α) : Measure α) := by
        simpa [G] using hω
      have hcoe : ((emp n ω : ProbabilityMeasure α) : Measure α) =
          (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i) := by
        have hemp : emp n ω =
            (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
              IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α) := by
          unfold emp
          exact dite_eq_left hn
        rw [hemp]
        rfl
      rw [hcoe, integral_emp ω f, le_div_iff₀ (Nat.cast_pos.mpr hn)] at hint
      exact hint
    refine (measure_mono hsub).trans ?_
    exact GetPiFunSetOfGeSum_Mul.le.OfRealMulExpMulNegPowIntegral_Exp.of.BoundedContinuousFunction
      f c n
  have hI : 0 < ∫ x, exp (f x) ∂μ := by
    have hge : ∀ x, exp (-‖f‖) ≤ exp (f x) := fun x => exp_le_exp.mpr (f.neg_norm_le_apply x)
    have hintc : Integrable (fun _ : α => exp (-‖f‖)) μ := integrable_const _
    have hint : Integrable (fun x => exp (f x)) μ := by
      refine ⟨(continuous_exp.comp f.continuous).aestronglyMeasurable, ?_⟩
      refine HasFiniteIntegral.of_bounded (C := exp ‖f‖) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr (f.apply_le_norm x)
    have hmono := integral_mono hintc hint (fun x => hge x)
    rw [integral_const, probReal_univ, one_smul] at hmono
    exact lt_of_lt_of_le (exp_pos _) hmono
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hlog : ENNReal.log (law n F) ≤
      ENNReal.log (ENNReal.ofReal (exp (-c * n) * (∫ x, exp (f x) ∂μ) ^ n)) :=
    log_monotone (hbound n hn)
  refine (mul_le_mul_of_nonneg_left hlog ?_).trans ?_
  · exact EReal.inv_nonneg_of_nonneg (by exact_mod_cast Nat.zero_le n)
  rw [log_ofReal_of_pos (by positivity)]
  have hlogR : log (exp (-c * n) * (∫ x, exp (f x) ∂μ) ^ n) =
      -c * n + n * log (∫ x, exp (f x) ∂μ) := by
    rw [Real.log_mul (exp_ne_zero _) (by positivity), Real.log_exp, Real.log_pow]
  rw [hlogR]
  have hcoeff : -c * (n : ℝ) + (n : ℝ) * log (∫ x, exp (f x) ∂μ) =
      (n : ℝ) * (-c + log (∫ x, exp (f x) ∂μ)) := by ring
  rw [hcoeff, EReal.coe_mul, ← mul_assoc]
  have hcancel : ((n : ℕ) : EReal)⁻¹ * ((n : ℝ) : EReal) = 1 := by
    rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_inv (n : ℝ), ← EReal.coe_mul]
    exact_mod_cast inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')
  rw [hcancel, one_mul]


-- created on 2026-11-02
