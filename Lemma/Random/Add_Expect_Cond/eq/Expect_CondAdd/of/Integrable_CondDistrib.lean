import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Syntax.Probability.Expectation.Elab
import Notation.Probability.ApplyRV
import Instance.Probability.Add
import Theorem.Probability.JointRv.AsRV
open MeasureTheory
open scoped ProbabilityTheory ApplyRV


@[path]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSpace 𝒮]
  {π : Measure Ω} [IsFiniteMeasure π]
  {a : Ω → α} {s : Ω → 𝒮} {b : Ω → β}
  {f : α → ℝ} {g : β → ℝ}
-- given
  («\sf{s}» : 𝒮)
  (hf : Integrable f (ProbabilityTheory.condDistrib a s π «\sf{s}»)) :
-- imply
  g b + 𝔼[a: π](f a | s = «\sf{s}») =
    𝔼[a: π](f a + g b | s = «\sf{s}») := by
-- proof
  funext ω
  simp only [Function.applyRV_apply, ProbabilityTheory.fun_add_real_apply, expectation_real,
    Expectation.asRV_function, Expectation.condEval]
  have hc : Integrable (fun _ : α => g (b ω))
      (ProbabilityTheory.condDistrib a s π «\sf{s}») :=
    integrable_const _
  rw [integral_add hf hc, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul, add_comm]


-- created on 2023-04-12
-- updated on 2026-11-12
