import Class.Probability.Rv.Part2
import Syntax.Order.Sup
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
open MeasureTheory
open scoped BigOperators


/--
Under a finite alphabet with counting reference measure, a uniform Finset-sum bound on g
is the continuous-action package Integrable (g x) plus a uniform Bochner-integral bound.
Used to apply dens / FunSMul Subset leaves from CountableMeasure sum-hypotheses.
-/
@[path]
private lemma main
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {g : ι → A → ℝ}
-- given
  (h : sup[x] (∑ u, g x u) < ∞) :
-- imply
  (∀ x, Integrable (g x) ReferenceMeasure.measure) ∧
    (sup[x] (∫ u, g x u ∂ReferenceMeasure.measure) < ∞) := by
-- proof
  have hμ : (ReferenceMeasure.measure : Measure A) = Measure.count :=
    CountableMeasure.measure_eq_count
  refine ⟨fun x => ?_, ?_⟩
  ·
    rw [hμ]
    apply integrable_count_iff.mpr
    apply Summable.of_finite
  ·
    obtain ⟨Cg, hUB⟩ := h
    refine ⟨Cg, ?_⟩
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    simpa [hμ, integral_count] using hUB (Set.mem_range_self x)


-- created on 2026-11-03
