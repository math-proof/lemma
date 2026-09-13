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
[sympy.Expectation](https://github.com/sympy/sympy/blob/master/sympy/stats/symbolic_probability.py)

Expectation of an observable `f : α → ENNReal` under a law `ν : Measure α` — the Lebesgue
integral of `f` against `ν`:

  `Expectation ν f = ∫⁻ a, f a ∂ν`

sympy's `Expectation` carries the distribution in its limits (`Expectation[a:θ](f(a))`
means `a ~ θ`); here the law is the explicit first argument. For a random variable
`x : Ω → α` with state measure `𝕡` the law is the pushforward `𝕡.map x`, so

  `Expectation (𝕡.map x) f = ∫⁻ ω, f (x ω) ∂𝕡`

Conditioning enters by taking the conditional law — e.g. `Expectation
(ReferenceMeasure.measure.withDensity (fun a ↦ 𝕡.condProb (x, y) (a, b))) f` is
`𝔼[f(x) | y = b]`.
-/
noncomputable def Expectation
    {α : Type*}
    [MeasurableSpace α]
    (ν : Measure α)
    (f : α → ENNReal) :
    ENNReal :=
  ∫⁻ a, f a ∂ν


/--
Canonical density `Pr(x)` of a single random variable (Radon–Nikodym derivative of its
law w.r.t. the canonical state measure). Equal a.e. to any witnessing density from
`PSpace.exists_distribution`. Lives in `MeasureTheory.Measure` (alongside `map` and
`rnDeriv`) so it reads in dot form `𝕡.prob x`, next to `𝕡.map x`.
-/
noncomputable def MeasureTheory.Measure.prob
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (𝕡 : Measure Ω)
    (x : Ω → α)
    [PSpace 𝕡 x] :
    α → ENNReal :=
  (𝕡.map x).rnDeriv ReferenceMeasure.measure


/--
Canonical conditional density `Pr(x | y)` of a joint random symbol `(x, y)`: the joint
density `𝕡.prob (x, y)` divided by the marginal density of the second component — the
Bayes formula `Pr(x | y) = Pr(x, y) / Pr(y)`. Lives in `MeasureTheory.Measure` so it
reads in dot form `𝕡.condProb (x, y)`, mirroring `𝕡.prob (x, y)`.
-/
noncomputable def MeasureTheory.Measure.condProb
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (𝕡 : Measure Ω)
    (xy : Ω → α × β)
    [PSpace 𝕡 xy] :
    α × β → ENNReal :=
  fun z ↦ 𝕡.prob xy z /
    (𝕡.map (fun ω ↦ (xy ω).2)).rnDeriv ReferenceMeasure.measure z.2


/--
The law of `x` equals the state measure with density `𝕡.prob x`: the
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
      ReferenceMeasure.measure.withDensity (𝕡.prob x) := by
  have hp : PSpace 𝕡 x := inferInstance
  obtain ⟨π, _, hlaw⟩ := hp.exists_distribution
  exact (Measure.withDensity_rnDeriv_eq (𝕡.map x) _
    (hlaw ▸ withDensity_absolutelyContinuous _ _)).symm


/-- An `x ~ D` hypothesis, together with an a.e. measurability proof for `x`, supplies the
`PSpace D.measure x` instance. -/
theorem Distributed.pspace
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {𝕡 : Measure Ω} [IsProbabilityMeasure 𝕡]
    {x : Ω → α} {π : α → ENNReal}
    {D : Distribution 𝕡 π}
    (h : x ~ D)
    (hx : AEMeasurable x 𝕡) :
    PSpace 𝕡 x :=
  { toIsProbabilityMeasure := inferInstance
    aemeasurable := hx
    exists_distribution := ⟨D.density, D, h⟩ }


/--
`x ~ D` is equivalent to the canonical density of `x` being a.e. equal to `D`'s density
(`𝕡.prob x =ᵐ[ReferenceMeasure.measure] π`).
-/
theorem Distributed_iff
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {𝕡 : Measure Ω}
    {x : Ω → α} {π : α → ENNReal}
    [PSpace 𝕡 x]
    (D : Distribution 𝕡 π) :
    x ~ D ↔ 𝕡.prob x =ᵐ[ReferenceMeasure.measure] π := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h : D.measure.map x =
        ReferenceMeasure.measure.withDensity D.density := h
    show (D.measure.map x).rnDeriv ReferenceMeasure.measure =ᵐ[ReferenceMeasure.measure] D.density
    rw [h]
    exact Measure.rnDeriv_withDensity _ D.measurable_density
  · exact (@PSpace.map_eq_withDensity_density Ω α _ _ 𝕡 x _).trans
      (withDensity_congr_ae h)
