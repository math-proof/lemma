import sympy.stats.symbolic_probability
import sympy.Basic
open MeasureTheory


/--
The law of `x` equals the state measure with density `π.prob x`: the
distribution in `SinglePSpace.exists_distribution` gives absolute continuity, and the
Radon–Nikodym theorem reconstructs the measure from its canonical derivative.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω} {x : Ω → α} [SinglePSpace π x] :
-- imply
  π.map x =
      ReferenceMeasure.measure.withDensity (π.prob x) := by
-- proof
  have hp : SinglePSpace π x := inferInstance
  obtain ⟨ρ, _, hlaw⟩ := hp.exists_distribution
  exact (Measure.withDensity_rnDeriv_eq (π.map x) _
    (hlaw ▸ withDensity_absolutelyContinuous _ _)).symm


-- created on 2026-10-07
