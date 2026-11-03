import Lemma.ENNReal.SatisfiesLDP_Map_DivCountVecPi_ToMeasure.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal
import Lemma.Random.MapPi.of.Measurable
import Initialize.Tactic.Attr.Basic
open ENNReal MeasureTheory Random Real


/--
On any probability space, the empirical frequencies of a finite measurable observable satisfy the
finite-alphabet large deviation principle. Cells of mass zero are allowed: the rate is `⊤` when a
frequency vector charges one of them. A Polish sample space is included. This is Sanov's theorem
for one finite partition.
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
  (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → (∀ a, ((μ.map φ) {a}).toReal = 0 → ν a = 0) → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / ((μ.map φ) {a}).toReal)))
  (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ∀ a, ((μ.map φ) {a}).toReal = 0 → ν a = 0) → I ν = ⊤) :
-- imply
  SatisfiesLDP (fun n => (Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n)) I :=
-- proof
by
  let : IsProbabilityMeasure (μ.map φ) := (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  let p : PMF α := (μ.map φ).toPMF
  have hto : p.toMeasure = μ.map φ := Measure.toPMF_toMeasure (μ.map φ)
  have hOn' : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → (∀ a, (p a).toReal = 0 → ν a = 0) → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (p a).toReal)) := by
    intro ν hge hsum hvan
    have hvan' : ∀ a, ((μ.map φ) {a}).toReal = 0 → ν a = 0 := by
      intro a ha
      exact hvan a (by simpa [p, Measure.toPMF_apply] using ha)
    rw [hOn ν hge hsum hvan']
    simp [p, Measure.toPMF_apply]
  have hOut' : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ∀ a, (p a).toReal = 0 → ν a = 0) → I ν = ⊤ := by
    intro ν hbad
    refine hOut ν ?_
    intro h
    refine hbad ⟨h.1, h.2.1, ?_⟩
    intro a ha
    exact h.2.2 a (by simpa [p, Measure.toPMF_apply] using ha)
  have hfinite := SatisfiesLDP_Map_DivCountVecPi_ToMeasure.of.All_Eq_Top.All_Eq_OfRealSum_Mul_LogDiv_ToReal hOn' hOut'
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


-- created on 2026-11-02
-- updated on 2026-11-03
