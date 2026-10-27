import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
import Theorem.Probability.SymbolicProbability.Part2
open MeasureTheory


export Expectation (expectation)


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

