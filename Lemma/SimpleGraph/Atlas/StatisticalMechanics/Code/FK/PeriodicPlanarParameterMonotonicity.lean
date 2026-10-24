import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarParameterMonotonicity
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.wiredBufferedMeasure_real_cylinder_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarParameterMonotonicity.lean)
-/
@[path]
private lemma wiredBufferedMeasure_real_cylinder_monotone_in_p_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {N m : Nat}
  {p1 p2 q : Real}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N <= m)
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hp12 : p1 <= p2)
  (hq : 1 <= q)
  (hS : IsIncreasing S) :
-- imply
  (P.wiredBufferedMeasure m hp1 hp1' (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) <= (P.wiredBufferedMeasure m hp2 hp2' (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_real_cylinder_monotone_in_p P hNm hp1 hp1' hp2 hp2' hp12 hq hS

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarParameterMonotonicity.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {N : Nat}
  {p1 p2 q : Real}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hp12 : p1 <= p2)
  (hq : 1 <= q)
  (hS : IsIncreasing S) :
-- imply
  (P.wiredBufferedInfiniteVolume hp1 hp1' (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) <= (P.wiredBufferedInfiniteVolume hp2 hp2' (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p P N hp1 hp1' hp2 hp2' hp12 hq hS

/--
[PeriodicGraph.wiredPercolationProbability_monotoneOn_of_cylinderApproximation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarParameterMonotonicity.lean)
-/
@[path]
private lemma wiredPercolationProbability_monotoneOn_of_cylinderApproximation_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hq : 1 <= q)
  (happrox : P.HasPercolationCylinderApproximation q) :
-- imply
  MonotoneOn (fun p => P.wiredPercolationProbability p q) (Ioo (0 : Real) 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolationProbability_monotoneOn_of_cylinderApproximation P hq happrox

/--
[PeriodicGraph.dualCritical_relation_of_cylinderApproximation_noCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarParameterMonotonicity.lean)
-/
@[path]
private lemma dualCritical_relation_of_cylinderApproximation_noCoexistence_eq
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
  (hq : 1 <= q)
  (happrox : P.HasPercolationCylinderApproximation q)
  (happroxDual : Pdual.HasPercolationCylinderApproximation q)
  (hcoverage : DualSubcriticalCoverage (fun p => Pdual.wiredPercolates p q) (P.criticalPoint q) q)
  (hnoCoexistence : DualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q) :
-- imply
  BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.dualCritical_relation_of_cylinderApproximation_noCoexistence P Pdual hpc hpcDual hq happrox happroxDual hcoverage hnoCoexistence


-- created on 2026-10-23
