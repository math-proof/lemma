import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalPlanarBridge
open Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangular_hexagonal_critical_and_decay_of_planar_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalPlanarBridge.lean)
-/
@[path]
private lemma triangular_hexagonal_critical_and_decay_of_planar_inputs_eq
  {q : Real}
-- given
  (hq : 1 <= q)
  (hcoverage : DualSubcriticalCoverage (fun r => hexagonal.wiredPercolates r q) (triangular.criticalPoint q) q)
  (hcoverageDual : DualSubcriticalCoverage (fun r => triangular.wiredPercolates r q) (hexagonal.criticalPoint q) q)
  (hnoCoexistence : DualNoCoexistence (fun r => triangular.wiredPercolates r q) (fun r => hexagonal.wiredPercolates r q) q) :
-- imply
  (triangularFKCriticalPolynomial q (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧ SubcriticalTwoPointExponentialDecay triangular q (triangular.criticalPoint q) ∧ SubcriticalTwoPointExponentialDecay hexagonal q (hexagonal.criticalPoint q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_hexagonal_critical_and_decay_of_planar_inputs hq hcoverage hcoverageDual hnoCoexistence


-- created on 2026-10-23
