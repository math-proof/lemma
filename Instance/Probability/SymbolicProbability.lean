import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
import Class.Probability.SymbolicProbability
open MeasureTheory


export Expectation (expectation)


/--
[sympy.Expectation](https://github.com/sympy/sympy/blob/master/sympy/stats/symbolic_probability.py)

Polymorphic expectation via `[Expectation β]`: write `expectation ν f` for
`f : α → β`.

* `β = ENNReal` — Lebesgue integral `∫⁻ a, f a ∂ν` (non-negative; existing lemmas)
* `β = EReal` — signed extended expectation via positive/negative parts
* `β = ℝ` — Bochner integral `∫ a, f a ∂ν` (meaningful when integrable)
* `β = ℂ` — Bochner integral `∫ a, f a ∂ν` (meaningful when integrable)
* complete real normed spaces `E` (e.g. `Θ →L[ℝ] ℝ`) — Bochner integral (low-priority fallback)
* vectors / tensors — componentwise (import `Instance.Probability.SymbolicMultivariateProbability`)

sympy's `Expectation` carries the distribution in its limits (`Expectation[a:θ](f(a))`
means `a ~ θ`); here the law is the explicit first argument. For a random variable
`x : Ω → α` with state measure `π` the law is the pushforward `π.map x`, so

  `expectation (π.map x) f = …`

Conditioning enters by taking the conditional law — e.g. `expectation
(ReferenceMeasure.measure.withDensity (fun a ↦ π.condProb (x, y) (a, b))) f` is
`𝔼[f(x) | y = b]`.
-/

noncomputable instance : Expectation ENNReal where
  expectation ν f := ∫⁻ a, f a ∂ν

