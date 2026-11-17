module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.EReal.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Class.Probability.Rv
public import Class.Probability.SymbolicProbability

open MeasureTheory


export Expectation (expectation)


@[expose] public section

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

/--
Signed extended-real expectation: `E f = E f⁺ - E f⁻`, where the positive/negative
parts are the non-negative observables `(fun a ↦ (f a).toENNReal)` and
`(fun a ↦ (-f a).toENNReal)`, integrated with the `ENNReal` instance of
`expectation`. Mathlib's `EReal` arithmetic sends the indeterminate `⊤ - ⊤` to `⊥`.
-/
noncomputable instance : Expectation EReal where
  expectation ν f := expectation ν (fun a ↦ (f a).toENNReal) - expectation ν (fun a ↦ (-f a).toENNReal)

/--
Complex (Bochner) expectation. Equals the classical integral when `f` is integrable;
Mathlib's Bochner integral is `0` when not integrable — treat integrability as a
side condition in theorems that need a meaningful value.
-/
noncomputable instance : Expectation ℂ where
  expectation ν f := ∫ a, f a ∂ν

/--
Real (Bochner) expectation. Equals the classical integral when `f` is integrable;
Mathlib's Bochner integral is `0` when not integrable — treat integrability as a
side condition in theorems that need a meaningful value.
-/
noncomputable instance : Expectation ℝ where
  expectation ν f := ∫ a, f a ∂ν

/--
Vector-valued (Bochner) expectation for any complete real normed space `E`
(e.g. `Θ →L[ℝ] ℝ` gradients), `expectation ν f = ∫ a, f a ∂ν`. Declared with low priority so
that the dedicated instances (`ℝ`, `ℂ`, and the componentwise `List.Vector` / `Tensor` ones
of `Instance.Probability.SymbolicMultivariateProbability`) are preferred wherever they apply;
for `ℝ` and `ℂ` it agrees definitionally with them.
-/
noncomputable instance (priority := low) instExpectationBochner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    Expectation E where
  expectation ν f := ∫ a, f a ∂ν
