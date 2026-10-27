import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic
open MeasureTheory StatMech StatMech.Onsager


/--
[ons_riemann_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodic.lean)
-/
@[path]
private lemma ons_riemann_periodic_eq
  {f : ℝ → ℝ}
-- given
  (hf : Continuous f)
  (hper : Function.Periodic f (2 * Real.pi)) :
-- imply
  Filter.Tendsto (fun n : ℕ => (2 * Real.pi / n) * ∑ k ∈ Finset.range n, f (2 * Real.pi * k / n)) Filter.atTop (nhds (∫ x in (0)..(2 * Real.pi), f x)) := by
-- proof
  apply StatMech.Onsager.ons_riemann_periodic f hf hper


-- created on 2026-10-23
