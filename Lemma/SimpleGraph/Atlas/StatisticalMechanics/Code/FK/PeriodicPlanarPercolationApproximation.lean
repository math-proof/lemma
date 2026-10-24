import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[reachable_induce_innerBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma reachable_induce_innerBoundary_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Set V}
  {x z : V}
-- given
  (hx : x ∈ S)
  (hz : z ∉ S)
  (hreach : G.Reachable x z) :
-- imply
  ∃ y : S, (G.induce S).Reachable ⟨x, hx⟩ y ∧ ∃ w : V, G.Adj y.1 w ∧ w ∉ S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.reachable_induce_innerBoundary G S hx hz hreach

/--
[PeriodicGraph.root_mem_orbitBox_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma root_mem_orbitBox_zero_eq
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  P.root ∈ P.orbitBox 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.root_mem_orbitBox_zero P

/--
[PeriodicGraph.bufferedRoot_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedRoot_val_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : Nat} :
-- imply
  (P.bufferedRoot n : V) = P.root := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRoot_val P n

/--
[PeriodicGraph.bufferedRootBoundaryEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedRootBoundaryEvent_isIncreasing_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : Nat} :
-- imply
  IsIncreasing (P.bufferedRootBoundaryEvent n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRootBoundaryEvent_isIncreasing P n

/--
[PeriodicGraph.openSub_bufferedRestrict_eq_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma openSub_bufferedRestrict_eq_induce_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : Nat}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  FK.openSub (P.bufferedGraph n) (P.bufferedRestrict n omega) = (P.openSubgraph omega).induce (P.orbitBox (P.bufferedRadius n) : Set V) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.openSub_bufferedRestrict_eq_induce P n omega

/--
[PeriodicGraph.bufferedReachable_iff_inducedReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedReachable_iff_inducedReachable_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : Nat}
  {omega : ConfigSpace (Sym2 V)}
  {x y : P.BufferedVertex n} :
-- imply
  (FK.openSub (P.bufferedGraph n) (P.bufferedRestrict n omega)).Reachable x y ↔ ((P.openSubgraph omega).induce (P.orbitBox (P.bufferedRadius n) : Set V)).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedReachable_iff_inducedReachable P n omega x y

/--
[PeriodicGraph.bufferedReachable_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedReachable_full_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : Nat}
  {omega : ConfigSpace (Sym2 V)}
  {x y : P.BufferedVertex n}
-- given
  (h : (FK.openSub (P.bufferedGraph n) (P.bufferedRestrict n omega)).Reachable x y) :
-- imply
  (P.openSubgraph omega).Reachable x.1 y.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedReachable_full P n omega h

/--
[PeriodicGraph.bufferedBoundary_reachable_of_reachable_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedBoundary_reachable_of_reachable_outside_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : Nat}
  {omega : ConfigSpace (Sym2 V)}
  {x z : V}
-- given
  (hx : x ∈ P.orbitBox (P.bufferedRadius n))
  (hz : z ∉ P.orbitBox (P.bufferedRadius n))
  (hreach : (P.openSubgraph omega).Reachable x z) :
-- imply
  ∃ y : P.BufferedVertex n, P.bufferedBoundary n y ∧ (FK.openSub (P.bufferedGraph n) (P.bufferedRestrict n omega)).Reachable ⟨x, hx⟩ y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedBoundary_reachable_of_reachable_outside P n omega hx hz hreach

/--
[PeriodicGraph.bufferedBoundary_not_mem_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedBoundary_not_mem_of_lt_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n m : Nat}
  {v : P.BufferedVertex m}
-- given
  (hnm : n < m)
  (hv : P.bufferedBoundary m v) :
-- imply
  v.1 ∉ P.orbitBox (P.bufferedRadius n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedBoundary_not_mem_of_lt P hnm v hv

/--
[PeriodicGraph.bufferedRootBoundaryCylinder_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedRootBoundaryCylinder_antitone_eq
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  Antitone (fun n => P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRootBoundaryCylinder_antitone P

/--
[PeriodicGraph.iInter_bufferedRootBoundaryCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma iInter_bufferedRootBoundaryCylinder_eq
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  (⋂ n : Nat, P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)) = P.percolationEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iInter_bufferedRootBoundaryCylinder P

/--
[PeriodicGraph.bufferedRootBoundaryCylinder_real_tendsto_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedRootBoundaryCylinder_real_tendsto_measure_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu] :
-- imply
  Tendsto (fun n => mu.real (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))) atTop (nhds (mu.real P.percolationEvent)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRootBoundaryCylinder_real_tendsto_measure P mu

/--
[PeriodicGraph.bufferedRootBoundaryCylinder_real_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma bufferedRootBoundaryCylinder_real_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  Tendsto (fun n => (P.wiredBufferedInfiniteVolume hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))) atTop (nhds (P.wiredPercolationProbability p q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRootBoundaryCylinder_real_tendsto P hp hp1 hq

/--
[PeriodicGraph.hasPercolationCylinderApproximation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma hasPercolationCylinderApproximation_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  P.HasPercolationCylinderApproximation q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.hasPercolationCylinderApproximation P hq

/--
[PeriodicGraph.wiredPercolationProbability_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma wiredPercolationProbability_monotoneOn_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  MonotoneOn (fun p => P.wiredPercolationProbability p q) (Ioo (0 : Real) 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolationProbability_monotoneOn P hq

/--
[PeriodicGraph.offCriticalSharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma offCriticalSharpness_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1) :
-- imply
  OffCriticalSharpness (fun p => P.wiredPercolates p q) (P.criticalPoint q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.offCriticalSharpness P hq hpc

/--
[PeriodicGraph.dualCritical_relation_of_noCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean)
-/
@[path]
private lemma dualCritical_relation_of_noCoexistence_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {q : Real}
-- given
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hq : 1 ≤ q)
  (hcoverage : DualSubcriticalCoverage (fun p => Pdual.wiredPercolates p q) (P.criticalPoint q) q)
  (hnoCoexistence : DualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q) :
-- imply
  BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.dualCritical_relation_of_noCoexistence P Pdual hpc hpcDual hq hcoverage hnoCoexistence


-- created on 2026-10-23
