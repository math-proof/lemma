import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
import Def.Probability.SymbolicProbability
open MeasureTheory


/--
Interface for expectation of `β`-valued observables under a law `ν : Measure α`.

Instances cover the scalar and product codomains used by sympy-style probability:
`ENNReal` (non-neg Lebesgue), `EReal` (signed extended), `ℂ` (Bochner), and
componentwise `List.Vector` / `Tensor` (see `Instance.Probability.SymbolicMultivariateProbability`).

Call sites use the exported field `expectation ν f` (same pattern as
`class Operate` / `operate`).
-/
class Expectation (β : Type*) where
  /-- Expectation of an observable `f : α → β` under `ν`. -/
  expectation : {α : Type*} → [MeasurableSpace α] → Measure α → (α → β) → β

