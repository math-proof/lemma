import Lemma.Random.IsProbabilityMeasure.of.Gt_0
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Initialize.Tactic.Attr.Basic
open Finset MeasureTheory Random
open scoped ENNReal


/--
The empirical probability measure depends measurably on the sample. For a positive sample size, the
map sending a tuple of points to the normalized sum of Dirac masses at those points is measurable
for the Giry σ-algebra on probability measures.
-/
@[path]
private lemma main
  [MeasurableSpace α]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  Measurable (fun ω : Fin n → α =>
    (⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
      IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α)) :=
-- proof
by
  refine Measurable.subtype_mk ?_
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum, Finset.sum_apply]
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_fun_sum (f := fun i (ω : Fin n → α) => Measure.dirac (ω i) s)
    Finset.univ
    (fun i _ => Measurable.comp (Measure.measurable_coe hs)
      (Measurable.comp Measure.measurable_dirac (measurable_pi_apply i)))


-- created on 2026-11-02
