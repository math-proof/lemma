import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicGraph.bufferedTwoPointEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma bufferedTwoPointEvent_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {N : ℕ}
  {x y : P.BufferedVertex N} :
-- imply
  IsIncreasing (P.bufferedTwoPointEvent N x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedTwoPointEvent_isIncreasing P N x y

/--
[PeriodicGraph.bufferedTwoPointCylinder_subset_twoPointEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma bufferedTwoPointCylinder_subset_twoPointEvent_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {N : ℕ}
  {x y : P.BufferedVertex N} :
-- imply
  P.bufferedCylinder N (P.bufferedTwoPointEvent N x y) ⊆ P.twoPointEvent x.1 y.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedTwoPointCylinder_subset_twoPointEvent P N x y

/--
[PeriodicGraph.freeBufferedInfiniteVolume_le_wired_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_le_wired_cylinder_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {N : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤ (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_le_wired_cylinder P N hp hp1 hq hS

/--
[PeriodicGraph.freeBufferedTwoPointCylinder_le_wiredTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma freeBufferedTwoPointCylinder_le_wiredTwoPoint_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {N : ℕ}
  {p q : ℝ}
  {x y : P.BufferedVertex N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) (P.bufferedCylinder N (P.bufferedTwoPointEvent N x y)) ≤ ENNReal.ofReal (P.wiredTwoPointProbability p q x.1 y.1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedTwoPointCylinder_le_wiredTwoPoint P N hp hp1 hq x y

/--
[PeriodicGraph.measurableSet_cluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma measurableSet_cluster_infinite_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x : V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_cluster_infinite P x

/--
[PeriodicGraph.measurableSet_hasInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma measurableSet_hasInfiniteCluster_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | P.HasInfiniteCluster omega} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_hasInfiniteCluster P

/--
[PeriodicGraph.freeBufferedPairShell_le_wiredTwoPointSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma freeBufferedPairShell_le_wiredTwoPointSum_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {N : ℕ}
  {p q : ℝ}
  {pairs : Finset (P.BufferedVertex N × P.BufferedVertex N)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) (P.bufferedPairShell N pairs) ≤ ∑ xy ∈ pairs, ENNReal.ofReal (P.wiredTwoPointProbability p q xy.1.1 xy.2.1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedPairShell_le_wiredTwoPointSum P N hp hp1 hq pairs

/--
[freeDualHasInfiniteCluster_of_shell_borelCantelli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma freeDualHasInfiniteCluster_of_shell_borelCantelli_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
  {shell : ℕ → Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hsum : (∑' n, (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) (shell n)) ≠ ⊤)
  (hplanar : ((dualConfigEquiv D.edgeDual) ⁻¹' {eta | Pdual.HasInfiniteCluster eta})ᶜ ⊆ limsup shell atTop) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) ((dualConfigEquiv D.edgeDual) ⁻¹' {eta | Pdual.HasInfiniteCluster eta}) = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeDualHasInfiniteCluster_of_shell_borelCantelli D hp hp1 hq shell hsum hplanar

/--
[freeDualHasInfiniteCluster_of_summable_shell_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma freeDualHasInfiniteCluster_of_summable_shell_bound_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
  {shell : ℕ → Set (ConfigSpace (Sym2 V))}
  {bound : ℕ → NNReal}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hbound : Summable bound)
  (hshell : ∀ n, (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) (shell n) ≤ bound n)
  (hplanar : ((dualConfigEquiv D.edgeDual) ⁻¹' {eta | Pdual.HasInfiniteCluster eta})ᶜ ⊆ limsup shell atTop) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) ((dualConfigEquiv D.edgeDual) ⁻¹' {eta | Pdual.HasInfiniteCluster eta}) = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeDualHasInfiniteCluster_of_summable_shell_bound D hp hp1 hq shell bound hbound hshell hplanar

/--
[freeDualHasInfiniteCluster_of_exponentialDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean)
-/
@[path]
private lemma freeDualHasInfiniteCluster_of_exponentialDecay_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {p q pc : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hppc : p < pc)
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q pc) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) ((dualConfigEquiv D.edgeDual) ⁻¹' {eta | Pdual.HasInfiniteCluster eta}) = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeDualHasInfiniteCluster_of_exponentialDecay D H hp hp1 hppc hq hdecay


-- created on 2026-10-23
