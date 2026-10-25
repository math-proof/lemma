import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicGraph.percolationEvent_pos_of_vertex_cluster_infinite_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma percolationEvent_pos_of_vertex_cluster_infinite_pos_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {x : V}
-- given
  (hconn : P.graph.Connected)
  (hfe : HasFiniteEnergy mu)
  (hx : 0 < mu {omega | (P.cluster omega x).Infinite}) :
-- imply
  0 < mu P.percolationEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.percolationEvent_pos_of_vertex_cluster_infinite_pos P hconn mu hfe x hx

/--
[PeriodicGraph.clusterInfinite_pos_of_clusterInfinite_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma clusterInfinite_pos_of_clusterInfinite_pos_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {x y : V}
-- given
  (hconn : P.graph.Connected)
  (hfe : HasFiniteEnergy mu)
  (hx : 0 < mu {omega | (P.cluster omega x).Infinite}) :
-- imply
  0 < mu {omega | (P.cluster omega y).Infinite} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterInfinite_pos_of_clusterInfinite_pos P hconn mu hfe x y hx

/--
[PeriodicGraph.clusterInfinite_real_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma clusterInfinite_real_pos_iff_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {x y : V}
-- given
  (hconn : P.graph.Connected)
  (hfe : HasFiniteEnergy mu) :
-- imply
  0 < mu.real {omega | (P.cluster omega x).Infinite} ↔ 0 < mu.real {omega | (P.cluster omega y).Infinite} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterInfinite_real_pos_iff P hconn mu hfe x y

/--
[PeriodicGraph.percolationEvent_pos_of_hasInfiniteCluster_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma percolationEvent_pos_of_hasInfiniteCluster_measure_eq_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hconn : P.graph.Connected)
  (hfe : HasFiniteEnergy mu)
  (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
-- imply
  0 < mu P.percolationEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.percolationEvent_pos_of_hasInfiniteCluster_measure_eq_one P hconn mu hfe hexists

/--
[dualConfigEquiv_setClosed_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma dualConfigEquiv_setClosed_setOpen_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {e : Sym2 W}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  setOpen e (dualConfigEquiv D.edgeDual omega) = dualConfigEquiv D.edgeDual (setClosed (D.edgeDual.symm e) omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualConfigEquiv_setClosed_setOpen D e omega

/--
[dualMeasure_hasFiniteEnergy_of_primal_singleClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma dualMeasure_hasFiniteEnergy_of_primal_singleClosed_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hclosed : ∀ e : Sym2 V, mu.map (setClosed e) ≪ mu) :
-- imply
  HasFiniteEnergy (D.dualMeasure mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_hasFiniteEnergy_of_primal_singleClosed D mu hclosed

/--
[freeDualPercolates_of_hasInfiniteCluster_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma freeDualPercolates_of_hasInfiniteCluster_measure_eq_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hinfinite : (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) ((dualConfigEquiv D.edgeDual) ⁻¹' {eta | Pdual.HasInfiniteCluster eta}) = 1) :
-- imply
  D.FreeDualPercolates p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeDualPercolates_of_hasInfiniteCluster_measure_eq_one D hp hp1 hq hinfinite

/--
[freeDualPercolates_of_shell_borelCantelli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma freeDualPercolates_of_shell_borelCantelli_eq
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
  D.FreeDualPercolates p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeDualPercolates_of_shell_borelCantelli D hp hp1 hq shell hsum hplanar

/--
[freeDualPercolates_of_summable_shell_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma freeDualPercolates_of_summable_shell_bound_eq
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
  D.FreeDualPercolates p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeDualPercolates_of_summable_shell_bound D hp hp1 hq shell bound hbound hshell hplanar

/--
[freeDualPercolates_of_exponentialDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma freeDualPercolates_of_exponentialDecay_eq
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
  D.FreeDualPercolates p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeDualPercolates_of_exponentialDecay D H hp hp1 hppc hq hdecay

/--
[dualSubcriticalCoverage_of_exponentialDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma dualSubcriticalCoverage_of_exponentialDecay_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q pc : ℝ}
-- given
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q pc) :
-- imply
  DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) pc q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualSubcriticalCoverage_of_exponentialDecay D H hq hdecay

/--
[bidirectionalSubcriticalCoverage_of_exponentialDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageUpgrade.lean)
-/
@[path]
private lemma bidirectionalSubcriticalCoverage_of_exponentialDecay_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {Hdual : PolynomialConnectionShells D.swap}
  {q pc pcDual : ℝ}
-- given
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q pc)
  (hdecayDual : SubcriticalTwoPointExponentialDecay Pdual q pcDual) :
-- imply
  DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) pc q ∧ DualSubcriticalCoverage (fun r => P.wiredPercolates r q) pcDual q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.bidirectionalSubcriticalCoverage_of_exponentialDecay D H Hdual hq hdecay hdecayDual


-- created on 2026-10-23
