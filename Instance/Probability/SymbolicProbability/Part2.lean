import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
import Theorem.Probability.SymbolicProbability
open MeasureTheory


export Expectation (expectation)


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

