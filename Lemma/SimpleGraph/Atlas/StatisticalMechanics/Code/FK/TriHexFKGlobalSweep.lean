import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
open Finset StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangleFKLocalOddsWeight_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma triangleFKLocalOddsWeight_fiber_eq
  {y0 y1 y2 : Real}
  {connectivity : ThreeTerminalConnectivity} :
-- imply
  (∑ omega : LocalConfig, if triangleFKLocalConnectivity omega = connectivity then triangleFKLocalOddsWeight y0 y1 y2 omega else 0) = triangleFKTerminalWeight y0 y1 y2 connectivity := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKLocalOddsWeight_fiber y0 y1 y2 connectivity

/--
[starFKLocalOddsWeight_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma starFKLocalOddsWeight_fiber_eq
  {q y0 y1 y2 : Real}
  {connectivity : ThreeTerminalConnectivity} :
-- imply
  (∑ omega : LocalConfig, if starFKLocalConnectivity omega = connectivity then starFKLocalOddsWeight q y0 y1 y2 omega else 0) = starFKTerminalWeight q y0 y1 y2 connectivity := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKLocalOddsWeight_fiber q y0 y1 y2 connectivity

/--
[finiteLocalConfig_fiber_sum_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma finiteLocalConfig_fiber_sum_eq_prod_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype Ω]
  [Fintype C]
  [DecidableEq C]
  {classify : Ω → C}
  {weight : Ω → Real}
  {sector : ι → C} :
-- imply
  (∑ config : ι → Ω, if (fun i => classify (config i)) = sector then ∏ i, weight (config i) else 0) = ∏ i, ∑ omega : Ω, if classify omega = sector i then weight omega else 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finiteLocalConfig_fiber_sum_eq_prod classify weight sector

/--
[triangleFKGlobalConfigSum_eq_sweepSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma triangleFKGlobalConfigSum_eq_sweepSum_eq
  [Fintype ι]
  [DecidableEq ι]
  {y0 y1 y2 : Real}
  {external : (ι → ThreeTerminalConnectivity) → Real} :
-- imply
  triangleFKGlobalConfigSum y0 y1 y2 external = triangleFKGlobalSweepSum y0 y1 y2 external := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKGlobalConfigSum_eq_sweepSum y0 y1 y2 external

/--
[starFKGlobalConfigSum_eq_sweepSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma starFKGlobalConfigSum_eq_sweepSum_eq
  [Fintype ι]
  [DecidableEq ι]
  {q y0 y1 y2 : Real}
  {external : (ι → ThreeTerminalConnectivity) → Real} :
-- imply
  starFKGlobalConfigSum q y0 y1 y2 external = starFKGlobalSweepSum q y0 y1 y2 external := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKGlobalConfigSum_eq_sweepSum q y0 y1 y2 external

/--
[triHexFK_globalSweep_sector_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma triHexFK_globalSweep_sector_identity_eq
  [Fintype ι]
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {sector : ι → ThreeTerminalConnectivity}
-- given
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  (y0 * y1 * y2) ^ Fintype.card ι * (∏ i, starFKTerminalWeight q y0Star y1Star y2Star (sector i)) = (q ^ 2) ^ Fintype.card ι * ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_globalSweep_sector_identity h0 h1 h2 hsurface sector

/--
[triHexFK_globalSweepSum_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma triHexFK_globalSweepSum_identity_eq
  [Fintype ι]
  [DecidableEq ι]
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {external : (ι → ThreeTerminalConnectivity) → Real}
-- given
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  (y0 * y1 * y2) ^ Fintype.card ι * starFKGlobalSweepSum q y0Star y1Star y2Star external = (q ^ 2) ^ Fintype.card ι * triangleFKGlobalSweepSum y0 y1 y2 external := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_globalSweepSum_identity h0 h1 h2 hsurface external

/--
[triHexFK_globalSweepRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma triHexFK_globalSweepRatio_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {external observable : (ι → ThreeTerminalConnectivity) → Real}
-- given
  (hq : q ≠ 0)
  (hyprod : y0 * y1 * y2 ≠ 0)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  starFKGlobalSweepRatio q y0Star y1Star y2Star external observable = triangleFKGlobalSweepRatio y0 y1 y2 external observable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_globalSweepRatio_eq hq hyprod h0 h1 h2 hsurface external observable

/--
[ThreeTerminalConnectivity.connects_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma connects_symm_eq
  {connectivity : ThreeTerminalConnectivity}
  {i j : Fin 3} :
-- imply
  connectivity.Connects i j ↔ connectivity.Connects j i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ThreeTerminalConnectivity.connects_symm connectivity i j

/--
[triHexFK_globalSweep_twoPointRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean)
-/
@[path]
private lemma triHexFK_globalSweep_twoPointRatio_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype V]
  [DecidableEq V]
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {terminal : ι → Fin 3 → V}
  {external : (ι → ThreeTerminalConnectivity) → Real}
  {x y : V}
-- given
  (hq : q ≠ 0)
  (hyprod : y0 * y1 * y2 ≠ 0)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  starFKGlobalSweepRatio q y0Star y1Star y2Star external (triHexFKTerminalTwoPointObservable terminal x y) = triangleFKGlobalSweepRatio y0 y1 y2 external (triHexFKTerminalTwoPointObservable terminal x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_globalSweep_twoPointRatio_eq hq hyprod h0 h1 h2 hsurface terminal external x y


-- created on 2026-10-23
