import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalAssembly
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[offCriticalSharpness_of_nonnegative_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma offCriticalSharpness_of_nonnegative_monotoneOn_eq
  [DecidableEq V]
  [DecidableEq W]
  {theta : Real -> Real}
  {pc : Real}
-- given
  (htheta : forall p, 0 <= theta p)
  (hmono : MonotoneOn theta (Ioo (0 : Real) 1))
  (hne : ({p | p ∈ Ioo (0 : Real) 1 /\ theta p = 0} : Set Real).Nonempty)
  (hpc : pc = sSup {p | p ∈ Ioo (0 : Real) 1 /\ theta p = 0}) :
-- imply
  OffCriticalSharpness (fun p => 0 < theta p) pc := by
-- proof
  apply StatMech.FK.PeriodicPlanar.offCriticalSharpness_of_nonnegative_monotoneOn htheta hmono hne hpc

/--
[PeriodicGraph.subcriticalSet_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma subcriticalSet_bddAbove_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real} :
-- imply
  BddAbove (P.subcriticalSet q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.subcriticalSet_bddAbove P q

/--
[PeriodicGraph.subcriticalSet_nonempty_of_criticalPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma subcriticalSet_nonempty_of_criticalPoint_pos_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hpc : 0 < P.criticalPoint q) :
-- imply
  (P.subcriticalSet q).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.subcriticalSet_nonempty_of_criticalPoint_pos P hpc

/--
[PeriodicGraph.criticalPoint_le_one_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma criticalPoint_le_one_of_pos_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hpc : 0 < P.criticalPoint q) :
-- imply
  P.criticalPoint q <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.criticalPoint_le_one_of_pos P hpc

/--
[PeriodicGraph.wiredPercolationProbability_eq_zero_of_lt_criticalPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma wiredPercolationProbability_eq_zero_of_lt_criticalPoint_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {q p : Real}
-- given
  (hpc : 0 < P.criticalPoint q)
  (hmono : MonotoneOn (fun r => P.wiredPercolationProbability r q) (Ioo (0 : Real) 1))
  (hp : p ∈ Ioo (0 : Real) 1)
  (hlt : p < P.criticalPoint q) :
-- imply
  P.wiredPercolationProbability p q = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolationProbability_eq_zero_of_lt_criticalPoint P hpc hmono hp hlt

/--
[PeriodicGraph.wiredPercolates_of_criticalPoint_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma wiredPercolates_of_criticalPoint_lt_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {q p : Real}
-- given
  (hp : p ∈ Ioo (0 : Real) 1)
  (hlt : P.criticalPoint q < p) :
-- imply
  P.wiredPercolates p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolates_of_criticalPoint_lt P hp hlt

/--
[PeriodicGraph.criticalPoint_lt_one_of_dualSubcriticalCoverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma criticalPoint_lt_one_of_dualSubcriticalCoverage_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {q : Real}
-- given
  (hq : 0 < q)
  (hpc : 0 < P.criticalPoint q)
  (hpcDual : 0 < Pdual.criticalPoint q)
  (hmonoDual : MonotoneOn (fun r => Pdual.wiredPercolationProbability r q) (Ioo (0 : Real) 1))
  (hcoverage : DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q) :
-- imply
  P.criticalPoint q < 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.criticalPoint_lt_one_of_dualSubcriticalCoverage P Pdual hq hpc hpcDual hmonoDual hcoverage

/--
[PeriodicGraph.criticalPoints_mem_Ioo_of_bidirectionalCoverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma criticalPoints_mem_Ioo_of_bidirectionalCoverage_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {q : Real}
-- given
  (hq : 0 < q)
  (hpc : 0 < P.criticalPoint q)
  (hpcDual : 0 < Pdual.criticalPoint q)
  (hmonoPrimal : MonotoneOn (fun r => P.wiredPercolationProbability r q) (Ioo (0 : Real) 1))
  (hmonoDual : MonotoneOn (fun r => Pdual.wiredPercolationProbability r q) (Ioo (0 : Real) 1))
  (hcoverage : DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
  (hcoverageDual : DualSubcriticalCoverage (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q) :
-- imply
  P.criticalPoint q ∈ Ioo (0 : Real) 1 /\ Pdual.criticalPoint q ∈ Ioo (0 : Real) 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.criticalPoints_mem_Ioo_of_bidirectionalCoverage P Pdual hq hpc hpcDual hmonoPrimal hmonoDual hcoverage hcoverageDual

/--
[PeriodicGraph.offCriticalSharpness_of_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma offCriticalSharpness_of_monotoneOn_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hmono : MonotoneOn (fun p => P.wiredPercolationProbability p q) (Ioo (0 : Real) 1)) :
-- imply
  OffCriticalSharpness (fun p => P.wiredPercolates p q) (P.criticalPoint q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.offCriticalSharpness_of_monotoneOn P hpc hmono

/--
[PeriodicGraph.dualCritical_relation_of_monotonicity_noCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalAssembly.lean)
-/
@[path]
private lemma dualCritical_relation_of_monotonicity_noCoexistence_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {q : Real}
-- given
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hq : 0 < q)
  (hmonoPrimal : MonotoneOn (fun p => P.wiredPercolationProbability p q) (Ioo (0 : Real) 1))
  (hmonoDual : MonotoneOn (fun p => Pdual.wiredPercolationProbability p q) (Ioo (0 : Real) 1))
  (hcoverage : DualSubcriticalCoverage (fun p => Pdual.wiredPercolates p q) (P.criticalPoint q) q)
  (hnoCoexistence : DualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q) :
-- imply
  BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.dualCritical_relation_of_monotonicity_noCoexistence P Pdual hpc hpcDual hq hmonoPrimal hmonoDual hcoverage hnoCoexistence


-- created on 2026-10-23
