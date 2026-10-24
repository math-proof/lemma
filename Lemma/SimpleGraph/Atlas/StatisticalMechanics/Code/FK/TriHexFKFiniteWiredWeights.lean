import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights
open Finset Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[wiredActiveRatio_eq_wiredFkProb_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma wiredActiveRatio_eq_wiredFkProb_lift_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred boundary]
  {p q : Real}
-- given
  (boundary : V -> Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (observable : ConfigSpace G.edgeSet -> Real) :
-- imply
  wiredActiveRatio G boundary p q observable = ∑ omega : ConfigSpace (Sym2 V), observable (restrictActive G omega) * wiredFkProb G boundary p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.wiredActiveRatio_eq_wiredFkProb_lift G boundary hp hp1 hq observable

/--
[triHexPlanarFiniteTriangle_localOddsProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_localOddsProduct_eq
  {n : Nat}
  {y : Real}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet} :
-- imply
  (∏ z, triangleFKLocalOddsWeight y y y (triHexPlanarFiniteTriangleConfigEquiv n omega z)) = ∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, if omega e then y else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_localOddsProduct n y omega

/--
[triHexPlanarFiniteTriangle_edgeProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_edgeProduct_eq
  {n : Nat}
  {p y : Real}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
-- given
  (hodds : p = (1 - p) * y) :
-- imply
  edgeProduct (triHexPlanarFiniteTriangleGraph n) p (extendActive (triHexPlanarFiniteTriangleGraph n) omega) = (∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) * ∏ z, triangleFKLocalOddsWeight y y y (triHexPlanarFiniteTriangleConfigEquiv n omega z) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_edgeProduct n hodds omega

/--
[triHexPlanarFiniteTriangle_wiredActiveWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_wiredActiveWeight_eq_eq
  {n : Nat}
  {p y q : Real}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
-- given
  (hodds : p = (1 - p) * y) :
-- imply
  wiredActiveWeight (triHexPlanarFiniteTriangleGraph n) (triHexPlanarFiniteBoundary n) p q omega = (∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) * (triHexFKTerminalWiredExternal q (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (fun z => triangleFKLocalConnectivity (triHexPlanarFiniteTriangleConfigEquiv n omega z)) * ∏ z, triangleFKLocalOddsWeight y y y (triHexPlanarFiniteTriangleConfigEquiv n omega z)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_wiredActiveWeight_eq n hodds omega

/--
[triHexPlanarFiniteTriangle_wiredActiveZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_wiredActiveZ_eq_eq
  {n : Nat}
  {p y q : Real}
-- given
  (hodds : p = (1 - p) * y) :
-- imply
  wiredActiveZ (triHexPlanarFiniteTriangleGraph n) (triHexPlanarFiniteBoundary n) p q = (∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) * triangleFKGlobalConfigSum y y y (triHexFKTerminalWiredExternal q (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_wiredActiveZ_eq n hodds

/--
[triHexPlanarFiniteTriangle_sectorBoundaryObservable_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_sectorBoundaryObservable_eq_indicator_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet} :
-- imply
  triHexFKTerminalBoundaryReachObservable (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0) (fun z => triangleFKLocalConnectivity (triHexPlanarFiniteTriangleConfigEquiv n omega z)) = triHexPlanarFiniteTriangleBoundaryReachIndicator n omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_sectorBoundaryObservable_eq_indicator n omega

/--
[triHexPlanarFiniteTriangle_wiredActiveNumer_boundary_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_wiredActiveNumer_boundary_eq_eq
  {n : Nat}
  {p y q : Real}
-- given
  (hodds : p = (1 - p) * y) :
-- imply
  wiredActiveNumer (triHexPlanarFiniteTriangleGraph n) (triHexPlanarFiniteBoundary n) p q (triHexPlanarFiniteTriangleBoundaryReachIndicator n) = (∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) * triangleFKGlobalConfigSum y y y (fun sector => triHexFKTerminalWiredExternal q (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) sector * triHexFKTerminalBoundaryReachObservable (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0) sector) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_wiredActiveNumer_boundary_eq n hodds

/--
[triHexPlanarFiniteTriangle_wiredActiveRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_wiredActiveRatio_eq_eq
  {n : Nat}
  {p y q : Real}
-- given
  (hp1 : p ≠ 1)
  (hodds : p = (1 - p) * y) :
-- imply
  wiredActiveRatio (triHexPlanarFiniteTriangleGraph n) (triHexPlanarFiniteBoundary n) p q (triHexPlanarFiniteTriangleBoundaryReachIndicator n) = triangleFKFiniteWiredBoundaryReachRatio q y y y (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_wiredActiveRatio_eq n hp1 hodds

/--
[triHexPlanarFiniteStar_isolatedCenterFactor_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_isolatedCenterFactor_product_eq
  {n : Nat}
  {q : Real}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet} :
-- imply
  (∏ z, starFKIsolatedCenterFactor q (triHexPlanarFiniteStarConfigEquiv n omega z)) = q ^ Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_isolatedCenterFactor_product n q omega

/--
[triHexPlanarFiniteStar_localOddsProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_localOddsProduct_eq
  {n : Nat}
  {q y : Real}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet} :
-- imply
  (∏ z, starFKLocalOddsWeight q y y y (triHexPlanarFiniteStarConfigEquiv n omega z)) = q ^ Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) * ∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, if omega e then y else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_localOddsProduct n q y omega

/--
[triHexPlanarFiniteStar_edgeProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_edgeProduct_eq
  {n : Nat}
  {p y : Real}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
-- given
  (hodds : p = (1 - p) * y) :
-- imply
  edgeProduct (triHexPlanarFiniteStarGraph n) p (extendActive (triHexPlanarFiniteStarGraph n) omega) = (∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) * ∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, if omega e then y else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_edgeProduct n hodds omega

/--
[triHexPlanarFiniteStar_wiredActiveWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_wiredActiveWeight_eq_eq
  {n : Nat}
  {p y q : Real}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
-- given
  (hodds : p = (1 - p) * y) :
-- imply
  wiredActiveWeight (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) p q omega = (∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) * (triHexFKTerminalWiredExternal q (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (fun z => starFKLocalConnectivity (triHexPlanarFiniteStarConfigEquiv n omega z)) * ∏ z, starFKLocalOddsWeight q y y y (triHexPlanarFiniteStarConfigEquiv n omega z)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_wiredActiveWeight_eq n hodds omega

/--
[triHexPlanarFiniteStar_wiredActiveZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_wiredActiveZ_eq_eq
  {n : Nat}
  {p y q : Real}
-- given
  (hodds : p = (1 - p) * y) :
-- imply
  wiredActiveZ (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) p q = (∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) * starFKGlobalConfigSum q y y y (triHexFKTerminalWiredExternal q (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_wiredActiveZ_eq n hodds

/--
[triHexPlanarFiniteStar_sectorBoundaryObservable_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_sectorBoundaryObservable_eq_indicator_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet} :
-- imply
  triHexFKTerminalBoundaryReachObservable (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0) (fun z => starFKLocalConnectivity (triHexPlanarFiniteStarConfigEquiv n omega z)) = triHexPlanarFiniteStarBoundaryReachIndicator n omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_sectorBoundaryObservable_eq_indicator n omega

/--
[triHexPlanarFiniteStar_wiredActiveNumer_boundary_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_wiredActiveNumer_boundary_eq_eq
  {n : Nat}
  {p y q : Real}
-- given
  (hodds : p = (1 - p) * y) :
-- imply
  wiredActiveNumer (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) p q (triHexPlanarFiniteStarBoundaryReachIndicator n) = (∏ e : (triHexPlanarFiniteStarGraph n).edgeSet, (1 - p)) * starFKGlobalConfigSum q y y y (fun sector => triHexFKTerminalWiredExternal q (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) sector * triHexFKTerminalBoundaryReachObservable (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0) sector) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_wiredActiveNumer_boundary_eq n hodds

/--
[triHexPlanarFiniteStar_wiredActiveRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_wiredActiveRatio_eq_eq
  {n : Nat}
  {p y q : Real}
-- given
  (hp1 : p ≠ 1)
  (hodds : p = (1 - p) * y) :
-- imply
  wiredActiveRatio (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) p q (triHexPlanarFiniteStarBoundaryReachIndicator n) = starFKFiniteWiredBoundaryReachRatio q y y y (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_wiredActiveRatio_eq n hp1 hodds

/--
[triHexPlanarFiniteTriangleWiredBoundaryProbability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleWiredBoundaryProbability_eq_eq
  {n : Nat}
  {p y q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hodds : p = (1 - p) * y) :
-- imply
  triHexPlanarFiniteTriangleWiredBoundaryProbability n p q = triangleFKFiniteWiredBoundaryReachRatio q y y y (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleWiredBoundaryProbability_eq n hp hp1 hq hodds

/--
[triHexPlanarFiniteStarWiredBoundaryProbability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarWiredBoundaryProbability_eq_eq
  {n : Nat}
  {p y q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hodds : p = (1 - p) * y) :
-- imply
  triHexPlanarFiniteStarWiredBoundaryProbability n p q = starFKFiniteWiredBoundaryReachRatio q y y y (triHexPlanarFiniteTerminalMap n) (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarWiredBoundaryProbability_eq n hp hp1 hq hodds

/--
[triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean)
-/
@[path]
private lemma triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous_eq
  {n : Nat}
  {q p : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Set.Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  triHexPlanarFiniteStarWiredBoundaryProbability n (BeffaraDC.dualParam p q) q = triHexPlanarFiniteTriangleWiredBoundaryProbability n p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous n hq hp hsurface


-- created on 2026-10-23
