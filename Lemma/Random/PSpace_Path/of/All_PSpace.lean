import Syntax.Probability.JointRv.Part6
import Initialize.Tactic.Attr.Basic
open MeasureTheory


/--
Path of a process with a.e. measurable coordinates is a.e. measurable (product σ-algebra).

Not an `instance`: synthesizing `IsProbabilityMeasure π` via `PSpace` would otherwise loop
through a metavariable process `X`.

Formerly `PSpace.of_process_path` in `Syntax/Probability/JointRv/Part6.lean`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α]
  {π : Measure Ω} {X : ℕ → Ω → α}
-- given
  (h : ∀ t, PSpace π (X t)) :
-- imply
  PSpace π (AsPathRV.path X) :=
-- proof
  {
    toIsProbabilityMeasure := (h 0).toIsProbabilityMeasure
    aemeasurable := (aemeasurable_pi_iff (μ := π)).2 fun t ↦ (h t).aemeasurable
  }


-- created on 2026-10-16
