import Lemma.Random.ExpectSMul.eq.ExpectSMulExpectCond.of.All_Eq.In_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Measure.Count.eq.ProdCountS
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import sympy.core.function
import sympy.vector.operators
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Filter Topology Measure
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 4000000


/--
`𝔼[∇ log π(a[t] | s[t]) • (γ ** @ r[t:])] =
  𝔼[∇ log π(a[t] | s[t]) • 𝔼[(γ ** @ r[t:]) | s[t], a[t]]]`
(law of iterated expectation on `(s[t], a[t])`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable
      ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).prodMk
        (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t))
      (by
        show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
        rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS])
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _θ =>
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
    𝔼[s, a : M θ](
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t], a[t]) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
-- proof
  intro hP _ _ _
  classical
  let _ : MeasurableSpace Θ := borel Θ
  have : ∀ t'', SinglePSpace (M θ) (a t'', s t'') := fun t'' => hP θ t''
  let ψ : S → A → Θ := fun x u =>
    ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log
  convert ExpectSMul.eq.ExpectSMulExpectCond.of.All_Eq.In_Ico (M := M) h₀ h₁ θ t ψ


-- created on 2023-04-01
-- updated on 2026-10-20
