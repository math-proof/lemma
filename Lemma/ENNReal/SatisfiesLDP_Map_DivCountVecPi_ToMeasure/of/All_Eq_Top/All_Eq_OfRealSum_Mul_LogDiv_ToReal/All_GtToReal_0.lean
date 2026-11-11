import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Lemma.ENNReal.In.inf.EReal.eq.In_SetOfAnd_Sum.eq.One_And.inf.ToEReal.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0
import Lemma.ENNReal.LowerSemicontinuous.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0
import Lemma.Real.Limsup.le.NegIn_SetOfAll_Ge_0AndSum.eq.OneAndIn.inf.ToEReal.of.All_GtToReal_0
import Lemma.Real.Negν.in.SetOfAll_Geν0AndSum_ν.eq.OneAndInν.inf.ToEReal.le.Liminf.of.IsOpen.All_GtToReal_0
import Structure.v1.Atlas.Probability.code.LargeDeviations
import Initialize.Tactic.Attr.Basic
open ENNReal Filter MeasureTheory Real


private lemma satisfiesLDP [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {μ : PMF α} {I : (α → ℝ) → ENNReal} (hμ : ∀ a, 0 < (μ a).toReal) (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (μ a).toReal))) (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1) → I ν = ⊤) :
  SatisfiesLDP (fun n => Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure)) I := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨LowerSemicontinuous.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0 hμ hOn hOut⟩
  ·
    intro U hU
    rw [In.inf.EReal.eq.In_SetOfAnd_Sum.eq.One_And.inf.ToEReal.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0 hμ hOn hOut]
    have heq : (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure)) U)) = (fun n : ℕ => ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U})) := by
      ext n
      have hf : Measurable (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) := measurable_of_finite _
      rw [Measure.map_apply hf hU.measurableSet]
      rfl
    simpa [heq] using Negν.in.SetOfAll_Geν0AndSum_ν.eq.OneAndInν.inf.ToEReal.le.Liminf.of.IsOpen.All_GtToReal_0 hμ hU
  ·
    intro F hF
    rw [In.inf.EReal.eq.In_SetOfAnd_Sum.eq.One_And.inf.ToEReal.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0 hμ hOn hOut]
    have heq : (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure)) F)) = (fun n : ℕ => ((n : EReal)⁻¹) * ENNReal.log ((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ F})) := by
      ext n
      have hf : Measurable (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) := measurable_of_finite _
      rw [Measure.map_apply hf hF.measurableSet]
      rfl
    simpa [heq] using Limsup.le.NegIn_SetOfAll_Ge_0AndSum.eq.OneAndIn.inf.ToEReal.of.All_GtToReal_0 hμ

/--
On a finite alphabet, the law of the empirical frequency satisfies a large deviation principle of
speed `n`. The rate is `ENNReal.ofReal` of relative entropy on probability vectors and `⊤` off them,
provided every reference mass is positive.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : PMF α}
  {I : (α → ℝ) → ENNReal}
-- given
  (hμ : ∀ a, 0 < (μ a).toReal)
  (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (μ a).toReal)))
  (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1) → I ν = ⊤) :
-- imply
  SatisfiesLDP (fun n => Measure.map (fun ω : Fin n → α => fun a => (countVec ω a : ℝ) / n) (Measure.pi fun _ : Fin n => μ.toMeasure)) I :=
-- proof
  satisfiesLDP hμ hOn hOut


-- created on 2026-11-02
