import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
open Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[criticalPoint_eq_of_dual_percolation_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationClosure.lean)
-/
@[path]
private lemma criticalPoint_eq_of_dual_percolation_equivalence_eq
  {primalPercolates dualPercolates : Real -> Prop}
  {q p pc pcDual : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hpc : pc ∈ Ioo (0 : Real) 1)
  (hsharp : OffCriticalSharpness primalPercolates pc)
  (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
  (hcriticalDual : dualParam pc q = pcDual)
  (hnoCoexistence : DualNoCoexistence primalPercolates dualPercolates q)
  (hequiv : primalPercolates p <-> dualPercolates (dualParam p q)) :
-- imply
  p = pc ∧ dualParam p q = pcDual := by
-- proof
  apply StatMech.FK.PeriodicPlanar.criticalPoint_eq_of_dual_percolation_equivalence hq hp hpc hsharp hsharpDual hcriticalDual hnoCoexistence hequiv

/--
[criticalPoint_eq_of_dual_percolation_equivalence_of_criticalDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationClosure.lean)
-/
@[path]
private lemma criticalPoint_eq_of_dual_percolation_equivalence_of_criticalDual_eq
  {primalPercolates dualPercolates : Real -> Prop}
  {q p pc pcDual : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hpc : pc ∈ Ioo (0 : Real) 1)
  (hsharp : OffCriticalSharpness primalPercolates pc)
  (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
  (hcriticalDual : dualParam pc q = pcDual)
  (hequiv : primalPercolates p <-> dualPercolates (dualParam p q)) :
-- imply
  p = pc ∧ dualParam p q = pcDual := by
-- proof
  apply StatMech.FK.PeriodicPlanar.criticalPoint_eq_of_dual_percolation_equivalence_of_criticalDual hq hp hpc hsharp hsharpDual hcriticalDual hequiv

/--
[triHexCriticalPolynomials_of_surfacePercolationEquivalence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationClosure.lean)
-/
@[path]
private lemma triHexCriticalPolynomials_of_surfacePercolationEquivalence_eq
  {q p pcTri pcHex : Real}
-- given
  (hq : 1 <= q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hpcTri : pcTri ∈ Ioo (0 : Real) 1)
  (hsharpTri : OffCriticalSharpness (fun r => triangular.wiredPercolates r q) pcTri)
  (hsharpHex : OffCriticalSharpness (fun r => hexagonal.wiredPercolates r q) pcHex)
  (hcriticalDual : dualParam pcTri q = pcHex)
  (hnoCoexistence : DualNoCoexistence (fun r => triangular.wiredPercolates r q) (fun r => hexagonal.wiredPercolates r q) q)
  (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0)
  (hequiv : TriHexSurfacePercolationEquivalence q p) :
-- imply
  p = pcTri ∧ triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCriticalPolynomials_of_surfacePercolationEquivalence hq hp hpcTri hsharpTri hsharpHex hcriticalDual hnoCoexistence hsurface hequiv

/--
[triangular_hexagonal_critical_of_surfacePercolationEquivalence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationClosure.lean)
-/
@[path]
private lemma triangular_hexagonal_critical_of_surfacePercolationEquivalence_eq
  {q p : Real}
-- given
  (hq : 1 <= q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hcriticalDual : dualParam (triangular.criticalPoint q) q = hexagonal.criticalPoint q)
  (hnoCoexistence : DualNoCoexistence (fun r => triangular.wiredPercolates r q) (fun r => hexagonal.wiredPercolates r q) q)
  (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0)
  (hequiv : TriHexSurfacePercolationEquivalence q p) :
-- imply
  p = triangular.criticalPoint q ∧ triangularFKCriticalPolynomial q (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds (hexagonal.criticalPoint q)) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_hexagonal_critical_of_surfacePercolationEquivalence hq hp hpcTri hpcHex hcriticalDual hnoCoexistence hsurface hequiv

/--
[triangular_hexagonal_critical_of_surfacePercolationEquivalence_of_criticalDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationClosure.lean)
-/
@[path]
private lemma triangular_hexagonal_critical_of_surfacePercolationEquivalence_of_criticalDual_eq
  {q p : Real}
-- given
  (hq : 1 <= q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hcriticalDual : dualParam (triangular.criticalPoint q) q = hexagonal.criticalPoint q)
  (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0)
  (hequiv : TriHexSurfacePercolationEquivalence q p) :
-- imply
  p = triangular.criticalPoint q ∧ triangularFKCriticalPolynomial q (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds (hexagonal.criticalPoint q)) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_hexagonal_critical_of_surfacePercolationEquivalence_of_criticalDual hq hp hpcTri hpcHex hcriticalDual hsurface hequiv


-- created on 2026-10-23
