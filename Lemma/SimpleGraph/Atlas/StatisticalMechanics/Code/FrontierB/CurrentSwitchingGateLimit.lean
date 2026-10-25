import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSwitchingGateLimit
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[currentSwitchingGate_tendsto_of_uniqueInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSwitchingGateLimit.lean)
-/
@[path]
private lemma currentSwitchingGate_tendsto_of_uniqueInfiniteCluster_eq
  {d : ℕ}
  {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hmu : WeakCurrentConverges mu muLim)
  (hnu : WeakCurrentConverges nu nuLim)
  (hunique : (independentSuperposedTraceLaw muLim nuLim : Measure _) (atLeastTwoInfinite d) = 0)
  (hQ : IsClopen Q) :
-- imply
  Tendsto (fun k => ((mu k).prod (nu k) : Measure _).real (currentPairTraceBoxGate Q k x y)) atTop (nhds ((muLim.prod nuLim : Measure _).real (currentPairTraceConnectionGate Q x y))) := by
-- proof
  apply StatMech.FrontierB.currentSwitchingGate_tendsto_of_uniqueInfiniteCluster hmu hnu hunique hQ x y

/--
[freeFreeCurrentSwitchingGate_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSwitchingGateLimit.lean)
-/
@[path]
private lemma freeFreeCurrentSwitchingGate_tendsto_eq
  {d : ℕ}
  {beta : ℝ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hunique : (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta) (infiniteFreeCurrentMeasure d beta hbeta) : Measure _) (atLeastTwoInfinite d) = 0)
  (hQ : IsClopen Q) :
-- imply
  Tendsto (fun k => let n := infiniteCurrentBoxSubsequence d beta hbeta k ((freeBoxCurrentMeasure d n beta hbeta).prod (freeBoxCurrentMeasure d n beta hbeta) : Measure _).real (currentPairTraceBoxGate Q k x y)) atTop (nhds (((infiniteFreeCurrentMeasure d beta hbeta).prod (infiniteFreeCurrentMeasure d beta hbeta) : Measure _).real (currentPairTraceConnectionGate Q x y))) := by
-- proof
  apply StatMech.FrontierB.freeFreeCurrentSwitchingGate_tendsto beta hbeta hunique hQ x y

/--
[freePlusCurrentSwitchingGate_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSwitchingGateLimit.lean)
-/
@[path]
private lemma freePlusCurrentSwitchingGate_tendsto_eq
  {d : ℕ}
  {beta : ℝ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hunique : (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta) (infinitePlusCurrentMeasure d beta hbeta) : Measure _) (atLeastTwoInfinite d) = 0)
  (hQ : IsClopen Q) :
-- imply
  Tendsto (fun k => let n := infiniteCurrentBoxSubsequence d beta hbeta k ((freeBoxCurrentMeasure d n beta hbeta).prod (plusBoxCurrentMeasure d n beta hbeta) : Measure _).real (currentPairTraceBoxGate Q k x y)) atTop (nhds (((infiniteFreeCurrentMeasure d beta hbeta).prod (infinitePlusCurrentMeasure d beta hbeta) : Measure _).real (currentPairTraceConnectionGate Q x y))) := by
-- proof
  apply StatMech.FrontierB.freePlusCurrentSwitchingGate_tendsto beta hbeta hunique hQ x y

/--
[plusPlusCurrentSwitchingGate_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSwitchingGateLimit.lean)
-/
@[path]
private lemma plusPlusCurrentSwitchingGate_tendsto_eq
  {d : ℕ}
  {beta : ℝ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hunique : (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta) (infinitePlusCurrentMeasure d beta hbeta) : Measure _) (atLeastTwoInfinite d) = 0)
  (hQ : IsClopen Q) :
-- imply
  Tendsto (fun k => let n := infiniteCurrentBoxSubsequence d beta hbeta k ((plusBoxCurrentMeasure d n beta hbeta).prod (plusBoxCurrentMeasure d n beta hbeta) : Measure _).real (currentPairTraceBoxGate Q k x y)) atTop (nhds (((infinitePlusCurrentMeasure d beta hbeta).prod (infinitePlusCurrentMeasure d beta hbeta) : Measure _).real (currentPairTraceConnectionGate Q x y))) := by
-- proof
  apply StatMech.FrontierB.plusPlusCurrentSwitchingGate_tendsto beta hbeta hunique hQ x y


-- created on 2026-10-23
