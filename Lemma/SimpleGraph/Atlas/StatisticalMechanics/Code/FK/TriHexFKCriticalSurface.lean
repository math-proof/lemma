import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKCriticalSurface
open MeasureTheory Set StatMech.Lattice StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexSurfacePercolationEquivalence_of_finiteWiredSweep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKCriticalSurface.lean)
-/
@[path]
private lemma triHexSurfacePercolationEquivalence_of_finiteWiredSweep_eq
  {q p : Real}
-- given
  (hq : 1 ≤ q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0) :
-- imply
  TriHexSurfacePercolationEquivalence q p := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexSurfacePercolationEquivalence_of_finiteWiredSweep hq hp hsurface

/--
[triHexSurfaceCandidate_criticalPoints_weaklyAligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKCriticalSurface.lean)
-/
@[path]
private lemma triHexSurfaceCandidate_criticalPoints_weaklyAligned_eq
  {q p : Real}
-- given
  (hq : 1 ≤ q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0) :
-- imply
  (p < triangular.criticalPoint q → dualParam p q ≤ hexagonal.criticalPoint q) ∧ (triangular.criticalPoint q < p → hexagonal.criticalPoint q ≤ dualParam p q) ∧ (dualParam p q < hexagonal.criticalPoint q → p ≤ triangular.criticalPoint q) ∧ (hexagonal.criticalPoint q < dualParam p q → triangular.criticalPoint q ≤ p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexSurfaceCandidate_criticalPoints_weaklyAligned hq hp hsurface

/--
[triangular_hexagonal_critical_of_finiteWiredSweep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKCriticalSurface.lean)
-/
@[path]
private lemma triangular_hexagonal_critical_of_finiteWiredSweep_eq
  {q p : Real}
-- given
  (hq : 1 ≤ q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hcriticalDual : dualParam (triangular.criticalPoint q) q = hexagonal.criticalPoint q)
  (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0) :
-- imply
  p = triangular.criticalPoint q ∧ triangularFKCriticalPolynomial q (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds (hexagonal.criticalPoint q)) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_hexagonal_critical_of_finiteWiredSweep hq hp hpcTri hpcHex hcriticalDual hsurface


-- created on 2026-10-23
