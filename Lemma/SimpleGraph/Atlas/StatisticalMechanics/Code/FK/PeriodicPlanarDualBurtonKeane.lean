import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualBurtonKeane.Part2
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicGraph.hasInfiniteCluster_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma hasInfiniteCluster_configTranslate_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.HasInfiniteCluster (P.configTranslate z omega) ↔ P.HasInfiniteCluster omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.hasInfiniteCluster_configTranslate P z omega

/--
[PeriodicGraph.hasInfiniteCluster_measure_eq_one_of_percolation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma hasInfiniteCluster_measure_eq_one_of_percolation_pos_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (herg : P.IsErgodic mu)
  (hpos : 0 < mu P.percolationEvent) :
-- imply
  mu {omega | P.HasInfiniteCluster omega} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.hasInfiniteCluster_measure_eq_one_of_percolation_pos P mu herg hpos

/--
[PeriodicGraph.hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hzeroOne : ∃ k : ℕ∞, mu {omega | P.numInfiniteClusters omega = k} = 1 ∧ (k = 0 ∨ k = 1))
  (hinfinite : mu {omega | P.HasInfiniteCluster omega} = 1) :
-- imply
  mu {omega | P.HasUniqueInfiniteCluster omega} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one P mu hzeroOne hinfinite

/--
[PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_hasUniqueInfiniteCluster_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_hasUniqueInfiniteCluster_measure_eq_one_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {p q : Real}
-- given
  (hconn : P.graph.Connected)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hperc : 0 < (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real P.percolationEvent) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | P.HasUniqueInfiniteCluster omega} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_hasUniqueInfiniteCluster_measure_eq_one E hconn hp hp1 hq hperc

/--
[dualConfigEquiv_setPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma dualConfigEquiv_setPattern_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {I : Finset (Sym2 W)}
  {eta : ConfigSpace ↥I}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  setPattern I eta (dualConfigEquiv D.edgeDual omega) = dualConfigEquiv D.edgeDual (setPattern (I.map D.edgeDual.symm.toEmbedding) (D.dualPatternPullback I eta) omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualConfigEquiv_setPattern D I eta omega

/--
[dualMeasure_setPattern_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma dualMeasure_setPattern_absolutelyContinuous_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {I : Finset (Sym2 W)}
  {eta : ConfigSpace ↥I}
-- given
  (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu) :
-- imply
  (D.dualMeasure mu).map (setPattern I eta) ≪ D.dualMeasure mu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_setPattern_absolutelyContinuous D mu hpattern I eta

/--
[dualMeasure_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma dualMeasure_isErgodic_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (herg : P.IsErgodic mu) :
-- imply
  Pdual.IsErgodic (D.dualMeasure mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_isErgodic D mu herg

/--
[dualMeasure_hasFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma dualMeasure_hasFiniteEnergy_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu) :
-- imply
  HasFiniteEnergy (D.dualMeasure mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_hasFiniteEnergy D mu hpattern

/--
[dualMeasure_numInfiniteClusters_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma dualMeasure_numInfiniteClusters_zero_or_one_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hconn : Pdual.graph.Connected)
  (herg : P.IsErgodic mu)
  (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu) :
-- imply
  ∃ k : ℕ∞, D.dualMeasure mu {omega | Pdual.numInfiniteClusters omega = k} = 1 ∧ (k = 0 ∨ k = 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_numInfiniteClusters_zero_or_one D hconn mu herg hpattern

/--
[dualMeasure_hasUniqueInfiniteCluster_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma dualMeasure_hasUniqueInfiniteCluster_measure_eq_one_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hconn : Pdual.graph.Connected)
  (herg : P.IsErgodic mu)
  (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu)
  (hinfinite : D.dualMeasure mu {omega | Pdual.HasInfiniteCluster omega} = 1) :
-- imply
  D.dualMeasure mu {omega | Pdual.HasUniqueInfiniteCluster omega} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_hasUniqueInfiniteCluster_measure_eq_one D hconn mu herg hpattern hinfinite

/--
[freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_measure_eq_one_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hconnDual : Pdual.graph.Connected)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hdualPerc : 0 < (D.dualMeasure (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)).real Pdual.percolationEvent) :
-- imply
  D.dualMeasure (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | Pdual.HasUniqueInfiniteCluster omega} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_measure_eq_one D hconnDual hp hp1 hq hdualPerc

/--
[freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_of_freeDualPercolates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_of_freeDualPercolates_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hconnDual : Pdual.graph.Connected)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hdual : D.FreeDualPercolates p q) :
-- imply
  D.dualMeasure (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | Pdual.HasUniqueInfiniteCluster omega} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_dual_hasUniqueInfiniteCluster_of_freeDualPercolates D hconnDual hp hp1 hq hdual

/--
[freeBufferedInfiniteVolume_commonUniqueInfiniteClusterEvent_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUniqueInfiniteClusterEvent_measure_eq_one_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hprimalPerc : 0 < (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real P.percolationEvent)
  (hdualPerc : 0 < (D.dualMeasure (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)).real Pdual.percolationEvent) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) D.commonUniqueInfiniteClusterEvent = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUniqueInfiniteClusterEvent_measure_eq_one D hconn hconnDual hp hp1 hq hprimalPerc hdualPerc


-- created on 2026-10-23
