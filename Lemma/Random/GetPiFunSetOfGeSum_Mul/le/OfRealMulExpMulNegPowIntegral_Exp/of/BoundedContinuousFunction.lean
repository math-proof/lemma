import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Initialize.Tactic.Attr.Basic
open ENNReal Finset MeasureTheory Real


/--
Markov's inequality applied to the exponential of a bounded continuous function, on an i.i.d. sample.
The probability that the sample sum exceeds `c * n` decays at the rate `c - log ∫ exp f`.
-/
@[path]
private lemma main
  [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
-- given
  (f : BoundedContinuousFunction α ℝ)
  (c : ℝ)
  (n : ℕ) :
-- imply
  (Measure.pi fun _ : Fin n => μ) {ω | c * n ≤ ∑ i, f (ω i)} ≤
    ENNReal.ofReal (exp (-c * n) * (∫ x, exp (f x) ∂μ) ^ n) :=
-- proof
by
  let ε : ℝ≥0∞ := ENNReal.ofReal (exp (c * n))
  let g : (Fin n → α) → ℝ≥0∞ := fun ω => ENNReal.ofReal (exp (∑ i, f (ω i)))
  have hset : {ω | c * (n : ℝ) ≤ ∑ i, f (ω i)} = {ω | ε ≤ g ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ε, g]
    rw [ofReal_le_ofReal_iff (exp_pos _).le, exp_le_exp]
  rw [hset]
  have hε0 : ε ≠ 0 := by
    simp [ε, ofReal_eq_zero, not_le, exp_pos]
  have hεtop : ε ≠ ∞ := ofReal_ne_top
  have hg : AEMeasurable g (Measure.pi fun _ : Fin n => μ) := by
    refine Measurable.aemeasurable ?_
    refine measurable_ofReal.comp ?_
    refine measurable_exp.comp ?_
    refine measurable_fun_sum Finset.univ fun i _ => ?_
    exact f.continuous.measurable.comp (measurable_pi_apply i)
  have hmarkov := meas_ge_le_lintegral_div (μ := Measure.pi fun _ : Fin n => μ) hg hε0 hεtop
  refine hmarkov.trans ?_
  have hint : Integrable (fun x => exp (f x)) μ := by
    refine ⟨(continuous_exp.comp f.continuous).aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := exp ‖f‖) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (f.apply_le_norm x)
  have hintn : Integrable (fun ω : Fin n → α => exp (∑ i, f (ω i))) (Measure.pi fun _ : Fin n => μ) := by
    have hrewrite : (fun ω : Fin n → α => exp (∑ i, f (ω i))) = fun ω => ∏ i, exp (f (ω i)) := by
      funext ω
      exact exp_sum Finset.univ fun i => f (ω i)
    rw [hrewrite]
    exact Integrable.fintype_prod fun _ => hint
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin n => μ] fun ω => exp (∑ i, f (ω i)) :=
    ae_of_all _ fun _ => (exp_pos _).le
  have hlin : ∫⁻ ω, g ω ∂(Measure.pi fun _ : Fin n => μ) =
      ENNReal.ofReal (∫ ω, exp (∑ i, f (ω i)) ∂(Measure.pi fun _ : Fin n => μ)) := by
    simpa [g] using (ofReal_integral_eq_lintegral_ofReal hintn hnn).symm
  rw [hlin]
  have hpow : ∫ ω, exp (∑ i, f (ω i)) ∂(Measure.pi fun _ : Fin n => μ) =
      (∫ x, exp (f x) ∂μ) ^ n := by
    have hrewrite : (fun ω : Fin n → α => exp (∑ i, f (ω i))) = fun ω => ∏ i, exp (f (ω i)) := by
      funext ω
      exact exp_sum Finset.univ fun i => f (ω i)
    rw [hrewrite]
    simpa using integral_fintype_prod_eq_pow (ι := Fin n) (fun x => exp (f x))
  rw [hpow]
  have hdiv : ENNReal.ofReal ((∫ x, exp (f x) ∂μ) ^ n) / ε =
      ENNReal.ofReal (exp (-c * n) * (∫ x, exp (f x) ∂μ) ^ n) := by
    unfold ε
    rw [← ofReal_div_of_pos (exp_pos _)]
    apply congrArg ENNReal.ofReal
    rw [div_eq_mul_inv, ← exp_neg, neg_mul, mul_comm]
  rw [hdiv]


-- created on 2026-11-02
