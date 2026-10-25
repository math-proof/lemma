import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusHomogeneous
open StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexFK_torus_homogeneous_activeSectorRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusHomogeneous.lean)
-/
@[path]
private lemma triHexFK_torus_homogeneous_activeSectorRatio_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {q p : Real}
  {observable : (TorusSite L → ThreeTerminalConnectivity) → Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  activeNumer (hexagonalTorusGraph L) (fun _ => BeffaraDC.dualParam p q) q (hexagonalTorusSectorObservable L observable) / activeZ (hexagonalTorusGraph L) (fun _ => BeffaraDC.dualParam p q) q = activeNumer (triangularTorusGraph L) (fun _ => p) q (triangularTorusSectorObservable L observable) / activeZ (triangularTorusGraph L) (fun _ => p) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_torus_homogeneous_activeSectorRatio_eq L hq hp hsurface observable

/--
[triHexFK_torus_homogeneous_activeTwoPointRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusHomogeneous.lean)
-/
@[path]
private lemma triHexFK_torus_homogeneous_activeTwoPointRatio_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {q p : Real}
  {x y : TorusSite L}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  activeNumer (hexagonalTorusGraph L) (fun _ => BeffaraDC.dualParam p q) q (hexagonalTorusActiveWhiteTwoPointIndicator L x y) / activeZ (hexagonalTorusGraph L) (fun _ => BeffaraDC.dualParam p q) q = activeNumer (triangularTorusGraph L) (fun _ => p) q (triangularTorusActiveTwoPointIndicator L x y) / activeZ (triangularTorusGraph L) (fun _ => p) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_torus_homogeneous_activeTwoPointRatio_eq L hq hp hsurface x y


-- created on 2026-10-23
