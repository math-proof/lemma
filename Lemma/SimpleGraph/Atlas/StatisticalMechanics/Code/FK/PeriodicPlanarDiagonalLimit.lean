import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.wiredBufferedRootBoundary_diag_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDiagonalLimit.lean)
-/
@[path]
private lemma wiredBufferedRootBoundary_diag_antitone_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  Antitone (fun n => (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedRootBoundary_diag_antitone P hp hp1 hq

/--
[PeriodicGraph.wiredBufferedRootBoundary_diag_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDiagonalLimit.lean)
-/
@[path]
private lemma wiredBufferedRootBoundary_diag_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  Tendsto (fun n => (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))) atTop (nhds (P.wiredPercolationProbability p q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedRootBoundary_diag_tendsto P hp hp1 hq

/--
[PeriodicGraph.wiredBufferedSetBoundary_diag_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDiagonalLimit.lean)
-/
@[path]
private lemma wiredBufferedSetBoundary_diag_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Set V}
  {N : Nat}
  {p q : Real}
-- given
  (hSfinite : S.Finite)
  (hS : S ⊆ (P.orbitBox (P.bufferedRadius N) : Set V))
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  Tendsto (fun n => (P.wiredBufferedMeasure (N + n) hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder (N + n) (P.bufferedSetBoundaryEvent S (N + n)))) atTop (nhds ((P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.setHitsInfinite S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedSetBoundary_diag_tendsto P S hSfinite N hS hp hp1 hq


-- created on 2026-10-23
