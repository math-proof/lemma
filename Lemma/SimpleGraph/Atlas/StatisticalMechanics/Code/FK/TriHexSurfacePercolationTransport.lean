import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport.Part4
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexTorusRadialSize_gt_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean)
-/
@[path]
private lemma triHexTorusRadialSize_gt_two_eq
  {n : Nat} :
-- imply
  2 < triHexTorusRadialSize n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusRadialSize_gt_two n

/--
[triHexFK_torus_radialReachProbability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean)
-/
@[path]
private lemma triHexFK_torus_radialReachProbability_eq_eq
  {p q : Real}
  {n : Nat}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  hexagonalTorusRadialReachProbability p q n = triangularTorusRadialReachProbability p q n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_torus_radialReachProbability_eq hq hp hsurface n

/--
[triangularTorusRadialPercolates_iff_hexagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean)
-/
@[path]
private lemma triangularTorusRadialPercolates_iff_hexagonal_eq
  {p q : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  TriangularTorusRadialPercolates p q ↔ HexagonalTorusRadialPercolates p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusRadialPercolates_iff_hexagonal hq hp hsurface

/--
[wiredPercolationProbability_eq_of_torusBufferedReachApproximation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean)
-/
@[path]
private lemma wiredPercolationProbability_eq_of_torusBufferedReachApproximation_eq
  {p q : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0)
  (happrox : TriHexTorusBufferedReachApproximation hp.1 hp.2 hq) :
-- imply
  triangular.wiredPercolationProbability p q = hexagonal.wiredPercolationProbability (BeffaraDC.dualParam p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.wiredPercolationProbability_eq_of_torusBufferedReachApproximation hq hp hsurface happrox

/--
[triHexSurfacePercolationEquivalence_of_torusBufferedReachApproximation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean)
-/
@[path]
private lemma triHexSurfacePercolationEquivalence_of_torusBufferedReachApproximation_eq
  {p q : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0)
  (happrox : TriHexTorusBufferedReachApproximation hp.1 hp.2 hq) :
-- imply
  TriHexSurfacePercolationEquivalence q p := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexSurfacePercolationEquivalence_of_torusBufferedReachApproximation hq hp hsurface happrox


-- created on 2026-10-23
