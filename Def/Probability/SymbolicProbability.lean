import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
open MeasureTheory


/--
[sympy.PSpace.probability](https://github.com/sympy/sympy/blob/master/sympy/stats/rv.py)

Probability of an event for a single random variable: the usual definition of probability
as a function of a condition. `Probability π x s` is the probability that `x` takes a value
in the event `s : Set α` — the value of the law of `x` (the pushforward of `π` along `x`)
at `s` — and is a non-negative scalar (`ENNReal`, at most `1` since `π` is a probability
measure):

  `Probability π x s = π.map x s`

For a measurable event this equals `π {ω | x ω ∈ s}` (`Measure.map_apply`);
a point condition is written as a set, e.g. `{a}` in the discrete case.
-/
noncomputable def Probability
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α)
    [SinglePSpace π x]
    (s : Set α) :
    ENNReal :=
  π.map x s


