import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
open StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularTorusActiveReachIndicator_eq_eventIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusBoundaryReach.lean)
-/
@[path]
private lemma triangularTorusActiveReachIndicator_eq_eventIndicator_eq
  {L : Nat}
  [Fact (2 < L)]
  {x : TorusSite L}
  {target : Finset (TorusSite L)} :
-- imply
  triangularTorusActiveReachIndicator L x target = (triangularTorusActiveReachEvent L x target).indicator (fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusActiveReachIndicator_eq_eventIndicator L x target

/--
[hexagonalTorusActiveWhiteReachIndicator_eq_eventIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusBoundaryReach.lean)
-/
@[path]
private lemma hexagonalTorusActiveWhiteReachIndicator_eq_eventIndicator_eq
  {L : Nat}
  [Fact (2 < L)]
  {x : TorusSite L}
  {target : Finset (TorusSite L)} :
-- imply
  hexagonalTorusActiveWhiteReachIndicator L x target = (hexagonalTorusActiveWhiteReachEvent L x target).indicator (fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusActiveWhiteReachIndicator_eq_eventIndicator L x target

/--
[triangularTorusSectorReachObservable_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusBoundaryReach.lean)
-/
@[path]
private lemma triangularTorusSectorReachObservable_eq_indicator_eq
  {L : Nat}
  [Fact (2 < L)]
  {x : TorusSite L}
  {target : Finset (TorusSite L)}
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet} :
-- imply
  triangularTorusSectorObservable L (triHexFKTerminalReachIndicator L x target) omega = triangularTorusActiveReachIndicator L x target omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusSectorReachObservable_eq_indicator L x target omega

/--
[hexagonalTorusSectorReachObservable_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusBoundaryReach.lean)
-/
@[path]
private lemma hexagonalTorusSectorReachObservable_eq_indicator_eq
  {L : Nat}
  [Fact (2 < L)]
  {x : TorusSite L}
  {target : Finset (TorusSite L)}
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet} :
-- imply
  hexagonalTorusSectorObservable L (triHexFKTerminalReachIndicator L x target) omega = hexagonalTorusActiveWhiteReachIndicator L x target omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusSectorReachObservable_eq_indicator L x target omega

/--
[triHexFK_torus_homogeneous_activeReachRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusBoundaryReach.lean)
-/
@[path]
private lemma triHexFK_torus_homogeneous_activeReachRatio_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {q p : Real}
  {x : TorusSite L}
  {target : Finset (TorusSite L)}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  activeNumer (hexagonalTorusGraph L) (fun _ => BeffaraDC.dualParam p q) q (hexagonalTorusActiveWhiteReachIndicator L x target) / activeZ (hexagonalTorusGraph L) (fun _ => BeffaraDC.dualParam p q) q = activeNumer (triangularTorusGraph L) (fun _ => p) q (triangularTorusActiveReachIndicator L x target) / activeZ (triangularTorusGraph L) (fun _ => p) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_torus_homogeneous_activeReachRatio_eq L hq hp hsurface x target

/--
[triHexFK_torus_homogeneous_activeReachProbability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusBoundaryReach.lean)
-/
@[path]
private lemma triHexFK_torus_homogeneous_activeReachProbability_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {q p : Real}
  {x : TorusSite L}
  {target : Finset (TorusSite L)}
-- given
  (hq : 0 < q)
  (hp : p ∈ Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  activeProbOf (hexagonalTorusGraph L) (fun _ => BeffaraDC.dualParam p q) q (hexagonalTorusActiveWhiteReachEvent L x target) = activeProbOf (triangularTorusGraph L) (fun _ => p) q (triangularTorusActiveReachEvent L x target) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_torus_homogeneous_activeReachProbability_eq L hq hp hsurface x target


-- created on 2026-10-23
