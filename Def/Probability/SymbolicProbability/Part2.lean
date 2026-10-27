import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
import Theorem.Probability.SymbolicProbability.Part3
open MeasureTheory


export Expectation (expectation)


/--
Canonical density `ℙ(x)` of a single random variable (Radon–Nikodym derivative of its
law w.r.t. the canonical state measure). Equal a.e. to any witnessing density from
`SinglePSpace.exists_distribution`. Lives in `MeasureTheory.Measure` (alongside `map` and
`rnDeriv`) so it reads in dot form `π.prob x`, next to `π.map x`.
-/
noncomputable def MeasureTheory.Measure.prob
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α)
    [SinglePSpace π x] :
    α → ENNReal :=
  (π.map x).rnDeriv ReferenceMeasure.measure


/--
Canonical conditional density `ℙ(x | y)` of a joint random symbol `(x, y)`: the joint
density `π.prob (x, y)` divided by the marginal density of the second component — the
Bayes formula `ℙ(x | y) = ℙ(x, y) / ℙ(y)`. Lives in `MeasureTheory.Measure` so it
reads in dot form `π.condProb (x, y)`, mirroring `π.prob (x, y)`.
-/
noncomputable def MeasureTheory.Measure.condProb
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (π : Measure Ω)
    (xy : Ω → α × β)
    [SinglePSpace π xy] :
    α × β → ENNReal :=
  fun z ↦ π.prob xy z /
    (π.map (fun ω ↦ (xy ω).2)).rnDeriv ReferenceMeasure.measure z.2


/--
Density of `x` evaluated at the realized value of `x` (random argument / magenta).
For each outcome `ω`:

  `(Measure.probRA π x) ω = Measure.prob π x (x ω)`

So the result is random (`Ω → ENNReal`). Binder form: `ℙ[π](x)`.
-/
noncomputable def MeasureTheory.Measure.probRA
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α)
    [SinglePSpace π x] :
    Ω → ENNReal :=
  fun ω ↦ π.prob x (x ω)


/--
Conditional density of the first component of `xy` at its realized value, given a
fixed observation of the second (magenta RA on the left). For each `ω`:

  `(Measure.probCond π xy y0) ω = Measure.condProb π xy ((xy ω).1, y0)`

Binder form: `ℙ[π](x | y = y0)` (joints via the macro).
-/
noncomputable def MeasureTheory.Measure.probCond
    {Ω α γ : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    (π : Measure Ω)
    (xy : Ω → α × γ)
    [SinglePSpace π xy]
    (y0 : γ) :
    Ω → ENNReal :=
  fun ω ↦ π.condProb xy ((xy ω).1, y0)


/--
Conditional density of the first component of `xy` at the realized joint value,
given the realized second component (magenta RA on both sides). For each `ω`:

  `(Measure.probCondRA π xy) ω = Measure.condProb π xy (xy ω)`

Binder form: `ℙ[π](x, y | z)` / `ℙ[π](x, y | z, w, …)`.
-/
noncomputable def MeasureTheory.Measure.probCondRA
    {Ω α γ : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    (π : Measure Ω)
    (xy : Ω → α × γ)
    [SinglePSpace π xy] :
    Ω → ENNReal :=
  fun ω ↦ π.condProb xy (xy ω)


/--
Conditional probability of a point of the first component of a joint `xy`
given its second component as a random argument (no fixed observation).
For each outcome `ω`:

  `(Measure.condProbRA π xy x0) ω = Measure.condProb π xy (x0, (xy ω).2)`

So the result is still random (`Ω → ENNReal`): a random expression in `xy.2`.
Binder form: `ℙ[π](x = x0 | y)` elaborates with `xy = (x, y)`.
-/
noncomputable def MeasureTheory.Measure.condProbRA
    {Ω α γ : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    (π : Measure Ω)
    (xy : Ω → α × γ)
    [SinglePSpace π xy]
    (x0 : α) :
    Ω → ENNReal :=
  fun ω ↦ π.condProb xy (x0, (xy ω).2)

