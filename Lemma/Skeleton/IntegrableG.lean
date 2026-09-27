import sympy.stats.markov_samples
import sympy.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Lemma.Skeleton.Any_Ge_0AndAll_All_LeNormG
import Lemma.Skeleton.MeasurableG.of.Measurable.Le
import Lemma.Measure.Measurable_Apply_PiLE
open MeasureTheory Measure


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d}
  {μ : Measure (ℕ → S × S)} [IsFiniteMeasure μ]
-- given
  (k j : ℕ) :
-- imply
  Integrable (fun ω => sk.G (sk.x k ω) (ω j)) μ := by
-- proof
  obtain ⟨C, -, hC⟩ := Skeleton.Any_Ge_0AndAll_All_LeNormG (sk := sk) k
  exact Integrable.of_bound ((Skeleton.MeasurableG.of.Measurable.Le (le_max_left k j) ((Measurable_Apply_PiLE (X := fun _ => S × S) j).mono (Filtration.piLE.mono (le_max_right k j)) le_rfl)).mono (Filtration.piLE.le _) le_rfl).aestronglyMeasurable C (ae_of_all _ fun ω => hC ω _)


-- created on 2026-09-26