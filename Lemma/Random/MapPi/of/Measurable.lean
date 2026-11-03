import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Fin.Pi_ToMeasure.of.EqSum
import Initialize.Tactic.Attr.Basic
open Fin MeasureTheory


private lemma map_freq [MeasurableSpace β] [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure β} [IsProbabilityMeasure μ] {φ : β → α} (hφ : Measurable φ) (n : ℕ) :
  (Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n) = (Measure.pi fun _ : Fin n => μ.map φ).map (fun η a => (countVec η a : ℝ) / n) := by
  let : IsProbabilityMeasure (μ.map φ) := (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  have hT : Measurable (fun ω : Fin n → β => fun i => φ (ω i)) := by
    rw [measurable_pi_iff]
    intro i
    exact hφ.comp (measurable_pi_apply i)
  have hpi : (Measure.pi fun _ : Fin n => μ).map (fun ω i => φ (ω i)) = Measure.pi fun _ : Fin n => μ.map φ :=
    Measure.pi_map_pi (μ := fun _ : Fin n => μ) (f := fun _ => φ) fun _ => hφ.aemeasurable
  have hcomp : (fun ω : Fin n → β => fun a => (countVec (fun i => φ (ω i)) a : ℝ) / n) = (fun η : Fin n → α => fun a => (countVec η a : ℝ) / n) ∘ (fun ω i => φ (ω i)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_of_finite _) hT, hpi]

/--
Pushing i.i.d. samples through a measurable finite-valued observable makes their empirical
frequency the finite-alphabet empirical frequency of the pushed law.
-/
@[path]
private lemma main
  [MeasurableSpace β]
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure β} [IsProbabilityMeasure μ]
  {φ : β → α}
-- given
  (hφ : Measurable φ)
  (n : ℕ) :
-- imply
  (Measure.pi fun _ : Fin n => μ).map (fun ω a => (countVec (fun i => φ (ω i)) a : ℝ) / n) =
    (Measure.pi fun _ : Fin n => μ.map φ).map (fun η a => (countVec η a : ℝ) / n) :=
-- proof
  map_freq hφ n


-- created on 2026-11-02
