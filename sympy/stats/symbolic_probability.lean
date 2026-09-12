import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import sympy.stats.rv
open MeasureTheory


/--
[sympy.PSpace.probability](https://github.com/sympy/sympy/blob/master/sympy/stats/rv.py)

Probability of an event for a single random variable: the usual definition of probability
as a function of a condition. `Probability 𝕡 x s` is the probability that `x` takes a value
in the event `s : Set α` — the value of the law of `x` (the pushforward of `𝕡` along `x`)
at `s` — and is a non-negative scalar (`ENNReal`, at most `1` since `𝕡` is a probability
measure):

  `Probability 𝕡 x s = 𝕡.map x s`

For a measurable event this equals `𝕡 {ω | x ω ∈ s}` (`Measure.map_apply`);
a point condition is written as a set, e.g. `{a}` in the discrete case.
-/
noncomputable def Probability
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (𝕡 : Measure Ω)
    (x : Ω → α)
    [PSpace 𝕡 x]
    (s : Set α) :
    ENNReal :=
  𝕡.map x s


/--
Canonical density `Pr(x)` of a single random variable (Radon–Nikodym derivative of its
law w.r.t. the canonical state measure). Equal a.e. to any witnessing density from
`PSpace.exists_distribution`.
-/
noncomputable def PSpace.density
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (𝕡 : Measure Ω)
    (x : Ω → α)
    [PSpace 𝕡 x] :
    α → ENNReal :=
  (𝕡.map x).rnDeriv ReferenceMeasure.measure


/--
The law of `x` equals the state measure with density `PSpace.density 𝕡 x`: the
distribution in `PSpace.exists_distribution` gives absolute continuity, and the
Radon–Nikodym theorem reconstructs the measure from its canonical derivative.
-/
theorem PSpace.map_eq_withDensity_density
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {𝕡 : Measure Ω}
    {x : Ω → α}
    [PSpace 𝕡 x] :
    𝕡.map x =
      ReferenceMeasure.measure.withDensity (PSpace.density 𝕡 x) := by
  have hp : PSpace 𝕡 x := inferInstance
  obtain ⟨π, _, hlaw⟩ := hp.exists_distribution
  exact (Measure.withDensity_rnDeriv_eq (𝕡.map x) _
    (hlaw ▸ withDensity_absolutelyContinuous _ _)).symm


/-- An `x ~ D` hypothesis supplies the `PSpace D.measure x` instance. -/
theorem Distributed.pspace
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {𝕡 : Measure Ω} [IsProbabilityMeasure 𝕡]
    {x : Ω → α} {π : α → ENNReal}
    {D : Distribution 𝕡 π}
    (h : x ~ D) :
    PSpace 𝕡 x :=
  { toIsProbabilityMeasure := inferInstance
    exists_distribution := ⟨D.density, D, h⟩ }


/--
`x ~ D` is equivalent to the canonical density of `x` being a.e. equal to `D`'s density
(`PSpace.density 𝕡 x =ᵐ[ReferenceMeasure.measure] π`).
-/
theorem Distributed_iff
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {𝕡 : Measure Ω}
    {x : Ω → α} {π : α → ENNReal}
    [PSpace 𝕡 x]
    (D : Distribution 𝕡 π) :
    x ~ D ↔ PSpace.density 𝕡 x =ᵐ[ReferenceMeasure.measure] π := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h : D.measure.map x =
        ReferenceMeasure.measure.withDensity D.density := h
    show (D.measure.map x).rnDeriv ReferenceMeasure.measure =ᵐ[ReferenceMeasure.measure] D.density
    rw [h]
    exact Measure.rnDeriv_withDensity _ D.measurable_density
  · exact (@PSpace.map_eq_withDensity_density Ω α _ _ 𝕡 x _).trans
      (withDensity_congr_ae h)
