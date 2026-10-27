import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceReduction
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[dualCritical_crossBounds_of_sharpness_strictNoCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceReduction.lean)
-/
@[path]
private lemma dualCritical_crossBounds_of_sharpness_strictNoCoexistence_eq
  {primalPercolates dualPercolates : Real → Prop}
  {pc pcDual q : Real}
-- given
  (hq : 0 < q)
  (hsharpPrimal : OffCriticalSharpness primalPercolates pc)
  (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
  (hcoverage : DualSubcriticalCoverage dualPercolates pc q)
  (hstrict : StrictDualNoCoexistence primalPercolates dualPercolates q) :
-- imply
  (∀ p ∈ Ioo (0 : Real) 1, p < pc → pcDual ≤ dualParam p q) ∧ (∀ p ∈ Ioo (0 : Real) 1, pc < p → dualParam p q ≤ pcDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualCritical_crossBounds_of_sharpness_strictNoCoexistence hq hsharpPrimal hsharpDual hcoverage hstrict

/--
[dualCritical_relation_of_sharpness_strictNoCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceReduction.lean)
-/
@[path]
private lemma dualCritical_relation_of_sharpness_strictNoCoexistence_eq
  {primalPercolates dualPercolates : Real → Prop}
  {pc pcDual q : Real}
-- given
  (hpc : pc ∈ Ioo (0 : Real) 1)
  (hpcDual : pcDual ∈ Ioo (0 : Real) 1)
  (hq : 0 < q)
  (hsharpPrimal : OffCriticalSharpness primalPercolates pc)
  (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
  (hcoverage : DualSubcriticalCoverage dualPercolates pc q)
  (hstrict : StrictDualNoCoexistence primalPercolates dualPercolates q) :
-- imply
  dualParam pc q = pcDual ∧ (pc / (1 - pc)) * (pcDual / (1 - pcDual)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualCritical_relation_of_sharpness_strictNoCoexistence hpc hpcDual hq hsharpPrimal hsharpDual hcoverage hstrict


-- created on 2026-10-23
