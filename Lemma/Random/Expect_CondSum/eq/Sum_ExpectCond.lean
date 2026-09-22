import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} {n : ℕ}
  {x : Ω → Fin n → α} {y : Ω → γ}
  {f : α → ENNReal}
-- given
  (hP : PSpace π (x, y))
  (hf : Measurable f)
  («y.bvar» : γ) :
-- imply
  𝔼[x: π](∑ k, f (x k) | y = «y.bvar») =
    ∑ k, 𝔼[x: π](f (x k) | y = «y.bvar») := by
-- proof
  simp only [Expectation.condRV, expectation_ennreal]
  have hfk : ∀ k : Fin n, Measurable (fun xv : Fin n → α ↦ f (xv k)) :=
    fun k => hf.comp (measurable_pi_apply k)
  exact lintegral_finsetSum (Finset.univ : Finset (Fin n)) fun k _ => hfk k


-- created on 2023-04-01
-- updated on 2026-09-21
