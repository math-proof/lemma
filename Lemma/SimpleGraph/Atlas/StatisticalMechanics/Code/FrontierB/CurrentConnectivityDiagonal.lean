import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[currentPairTraceBoxGate_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityDiagonal.lean)
-/
@[path]
private lemma currentPairTraceBoxGate_mono_eq
  {d : ℕ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d} :
-- imply
  Monotone (fun n => currentPairTraceBoxGate Q n x y) := by
-- proof
  apply StatMech.FrontierB.currentPairTraceBoxGate_mono Q x y

/--
[iUnion_currentPairTraceBoxGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityDiagonal.lean)
-/
@[path]
private lemma iUnion_currentPairTraceBoxGate_eq
  {d : ℕ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d} :
-- imply
  (⋃ n, currentPairTraceBoxGate Q n x y) = currentPairTraceConnectionGate Q x y := by
-- proof
  apply StatMech.FrontierB.iUnion_currentPairTraceBoxGate Q x y

/--
[isClopen_currentPairTraceBoxGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityDiagonal.lean)
-/
@[path]
private lemma isClopen_currentPairTraceBoxGate_eq
  {d : ℕ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {n : ℕ}
  {x y : Site d}
-- given
  (hQ : IsClopen Q) :
-- imply
  IsClopen (currentPairTraceBoxGate Q n x y) := by
-- proof
  apply StatMech.FrontierB.isClopen_currentPairTraceBoxGate hQ n x y

/--
[currentPairTraceBoxGate_diagonal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityDiagonal.lean)
-/
@[path]
private lemma currentPairTraceBoxGate_diagonal_tendsto_eq
  {d : ℕ}
  {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hmu : WeakCurrentConverges mu muLim)
  (hnu : WeakCurrentConverges nu nuLim)
  (hQ : IsClopen Q)
  (hno : CurrentPairConnectivityNoEscape mu nu Q x y) :
-- imply
  Tendsto (fun k => ((mu k).prod (nu k) : Measure _).real (currentPairTraceBoxGate Q k x y)) atTop (nhds ((muLim.prod nuLim : Measure _).real (currentPairTraceConnectionGate Q x y))) := by
-- proof
  apply StatMech.FrontierB.currentPairTraceBoxGate_diagonal_tendsto hmu hnu hQ x y hno


-- created on 2026-10-23
