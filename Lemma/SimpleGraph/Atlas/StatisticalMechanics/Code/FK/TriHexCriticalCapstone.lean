import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexCriticalCapstone
open Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangular_hexagonal_critical_and_decay_of_finiteWiredSweep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalCapstone.lean)
-/
@[path]
private lemma triangular_hexagonal_critical_and_decay_of_finiteWiredSweep_eq
  {q p : Real}
-- given
  (hq : 1 ≤ q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hcriticalDual : dualParam (triangular.criticalPoint q) q = hexagonal.criticalPoint q)
  (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0) :
-- imply
  (p = triangular.criticalPoint q ∧ triangularFKCriticalPolynomial q (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧ SubcriticalTwoPointExponentialDecay triangular q (triangular.criticalPoint q) ∧ SubcriticalTwoPointExponentialDecay hexagonal q (hexagonal.criticalPoint q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_hexagonal_critical_and_decay_of_finiteWiredSweep hq hp hpcTri hpcHex hcriticalDual hsurface

/--
[triangular_hexagonal_critical_and_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalCapstone.lean)
-/
@[path]
private lemma triangular_hexagonal_critical_and_decay_eq
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hcriticalDual : dualParam (triangular.criticalPoint q) q = hexagonal.criticalPoint q) :
-- imply
  (triangularFKCriticalPolynomial q (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧ SubcriticalTwoPointExponentialDecay triangular q (triangular.criticalPoint q) ∧ SubcriticalTwoPointExponentialDecay hexagonal q (hexagonal.criticalPoint q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_hexagonal_critical_and_decay hq hpcTri hpcHex hcriticalDual


-- created on 2026-10-23
