import Lemma.ENNReal.SatisfiesLDP_Map_DivCountVecPi_ToMeasure.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0
import Lemma.Random.MapPi.of.Measurable
import Initialize.Tactic.Attr.Basic
open ENNReal MeasureTheory Random Real


private lemma satisfies [MeasurableSpace β] [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure β} [IsProbabilityMeasure μ] {φ : β → α} {I : (α → ℝ) → ENNReal} (hφ : Measurable φ) (hμ : ∀ a, 0 < ((μ.map φ) {a}).toReal) (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / ((μ.map φ) {a}).toReal))) (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1) → I ν = ⊤) :
  SatisfiesLDP (fun n => (Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n)) I := by
  let : IsProbabilityMeasure (μ.map φ) := (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  let p : PMF α := (μ.map φ).toPMF
  have hto : p.toMeasure = μ.map φ := Measure.toPMF_toMeasure (μ.map φ)
  have hpos : ∀ a, 0 < (p a).toReal := by
    intro a
    simpa [p, Measure.toPMF_apply] using hμ a
  have hOn' : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (p a).toReal)) := by
    intro ν hge hsum
    rw [hOn ν hge hsum]
    simp [p, Measure.toPMF_apply]
  have hfinite := SatisfiesLDP_Map_DivCountVecPi_ToMeasure.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal.All_GtToReal_0 hpos hOn' hOut
  have heq : ∀ n, (Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n) = Measure.map (fun η : Fin n → α => fun a => (countVec η a : ℝ) / n) (Measure.pi fun _ : Fin n => p.toMeasure) := by
    intro n
    rw [MapPi.of.Measurable hφ n]
    simp [hto]
  refine ⟨hfinite.isRateFunction, ?_, ?_⟩
  ·
    intro U hU
    have hfun : (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (((Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n)) U)) = (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((Measure.map (fun η : Fin n → α => fun a => (countVec η a : ℝ) / n) (Measure.pi fun _ : Fin n => p.toMeasure)) U)) := by
      ext n
      rw [heq n]
    simpa [hfun] using hfinite.lower_bound U hU
  ·
    intro F hF
    have hfun : (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (((Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n)) F)) = (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((Measure.map (fun η : Fin n → α => fun a => (countVec η a : ℝ) / n) (Measure.pi fun _ : Fin n => p.toMeasure)) F)) := by
      ext n
      rw [heq n]
    simpa [hfun] using hfinite.upper_bound F hF

/--
On any probability space, the empirical frequencies of a finite measurable observable satisfy the
finite-alphabet large deviation principle, provided every cell has positive mass. A Polish sample
space is included. This is Sanov's theorem for one finite partition.
-/
@[path]
private lemma main
  [MeasurableSpace β]
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure β} [IsProbabilityMeasure μ]
  {φ : β → α}
  {I : (α → ℝ) → ENNReal}
-- given
  (hφ : Measurable φ)
  (hμ : ∀ a, 0 < ((μ.map φ) {a}).toReal)
  (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / ((μ.map φ) {a}).toReal)))
  (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1) → I ν = ⊤) :
-- imply
  SatisfiesLDP (fun n => (Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n)) I :=
-- proof
  satisfies hφ hμ hOn hOut


-- created on 2026-11-02
