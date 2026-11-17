module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.EReal.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Class.Probability.Rv
public section

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

