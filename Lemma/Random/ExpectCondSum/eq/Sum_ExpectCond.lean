import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorem.Probability.CondExpectation
import Initialize.Tactic.Attr.Basic
import Theorem.Probability.JointRv.AsRV
open MeasureTheory


@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} [IsFiniteMeasure π] {n : ℕ}
  [Nonempty (Fin n → α)] [StandardBorelSpace (Fin n → α)]
  {x : Ω → Fin n → α} {y : Ω → γ}
  {f : α → ENNReal}
-- given
  (hf : Measurable f)
  («\sf{y}» : γ) :
-- imply
  𝔼[x: π](∑ k, f (x k) | y = «\sf{y}») =
    ∑ k, 𝔼[x: π](f (x k) | y = «\sf{y}») := by
-- proof
  simp only [Expectation.asRV_function, Expectation.condEval, expectation_ennreal]
  have hfk : ∀ k : Fin n, Measurable (fun xv : Fin n → α ↦ f (xv k)) :=
    fun k => hf.comp (measurable_pi_apply k)
  exact lintegral_finsetSum (Finset.univ : Finset (Fin n)) fun k _ => hfk k


-- created on 2023-04-01
-- updated on 2026-11-13
