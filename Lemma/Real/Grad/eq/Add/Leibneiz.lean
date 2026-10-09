import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import sympy.Basic
open MeasureTheory
open scoped Topology


@[path]
private lemma main
  {f g h : ℝ → ℝ}
  {x g' h' : ℝ}
-- given
  (hf : Continuous f)
  (hg : HasDerivAt g g' x)
  (hh : HasDerivAt h h' x) :
-- imply
  deriv (fun x => ∫ t in g x..h x, f t) x = f (h x) * h' - f (g x) * g' := by
-- proof
  have h_int : IntervalIntegrable f volume (g x) (h x) :=
    hf.intervalIntegrable _ _
  have hma : StronglyMeasurableAtFilter f (𝓝 (g x)) :=
    hf.stronglyMeasurableAtFilter volume _
  have hmb : StronglyMeasurableAtFilter f (𝓝 (h x)) :=
    hf.stronglyMeasurableAtFilter volume _
  have hfd :=
    intervalIntegral.integral_hasFDerivAt h_int hma hmb hf.continuousAt hf.continuousAt
  have hpair : HasDerivAt (fun x => (g x, h x)) (g', h') x :=
    HasDerivAt.prodMk hg hh
  convert (hfd.comp_hasDerivAt x hpair).deriv using 1
  · rfl
  ·
    simp [smul_eq_mul]
    ring


-- created on 2026-10-08
