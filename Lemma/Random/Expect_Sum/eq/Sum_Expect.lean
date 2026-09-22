import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω} {n : ℕ}
  {x : Ω → Fin n → α}
  {f : α → ENNReal}
-- given
  (hP : PSpace π x)
  (hf : Measurable f) :
-- imply
  𝔼[x: π](∑ k, f (x k)) =
    ∑ k, 𝔼[x: π](f (x k)) := by
-- proof
  simp only [Expectation.ofRV, expectation_ennreal]
  have hfk : ∀ k : Fin n, Measurable (fun xv : Fin n → α ↦ f (xv k)) :=
    fun k => hf.comp (measurable_pi_apply k)
  exact lintegral_finsetSum (Finset.univ : Finset (Fin n)) fun k _ => hfk k


-- created on 2023-04-01
-- updated on 2026-09-21
