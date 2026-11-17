/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/KrylovBogolyubov.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

open MeasureTheory

namespace MathlibExt.Dynamics.Ergodic.KrylovBogolyubovWanted

/-!
# Krylov–Bogolyubov theorem

Invariant Borel probability measures for continuous self-maps of compact
metric spaces.
-/

/-- Cesàro average of Dirac masses along the forward orbit of `x₀` under `T`. -/
noncomputable def kbAvg
    {X : Type*} [MeasurableSpace X] (T : X → X) (x₀ : X) (n : ℕ) : Measure X :=
  ((n + 1 : ℕ) : ENNReal)⁻¹ • ∑ k ∈ Finset.range (n + 1), Measure.dirac (T^[k] x₀)

end MathlibExt.Dynamics.Ergodic.KrylovBogolyubovWanted
end
