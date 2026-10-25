import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure.Part2
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.freeWiredIncreasingCylinderAgreementOffCountable_of_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma freeWiredIncreasingCylinderAgreementOffCountable_of_logistic_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  P.FreeWiredIncreasingCylinderAgreementOffCountable q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeWiredIncreasingCylinderAgreementOffCountable_of_logistic P hagrees

/--
[PeriodicGraph.freeWiredBoundaryCylinderAgreementOffCountable_of_increasingCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma freeWiredBoundaryCylinderAgreementOffCountable_of_increasingCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountable q) :
-- imply
  P.FreeWiredBoundaryCylinderAgreementOffCountable q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeWiredBoundaryCylinderAgreementOffCountable_of_increasingCylinders P hagrees

/--
[PeriodicGraph.freeWiredPercolationAgreementOffCountable_of_boundaryCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma freeWiredPercolationAgreementOffCountable_of_boundaryCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hcyl : P.FreeWiredBoundaryCylinderAgreementOffCountable q) :
-- imply
  P.FreeWiredPercolationAgreementOffCountable q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeWiredPercolationAgreementOffCountable_of_boundaryCylinders P hcyl

/--
[PeriodicGraph.freeWiredPercolationAgreementOffCountable_of_increasingCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma freeWiredPercolationAgreementOffCountable_of_increasingCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountable q) :
-- imply
  P.FreeWiredPercolationAgreementOffCountable q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeWiredPercolationAgreementOffCountable_of_increasingCylinders P hagrees

/--
[PeriodicPlanarDualPair.freeCommonNoCoexistence_of_commonUniqueNotFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma freeCommonNoCoexistence_of_commonUniqueNotFull_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 ≤ q)
  (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent ≠ 1) :
-- imply
  D.FreeCommonNoCoexistence q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeCommonNoCoexistence_of_commonUniqueNotFull D hconn hconnDual hq hnotFull

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffield_offCountableAgreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_sheffield_offCountableAgreement_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 ≤ q)
  (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent = 0)
  (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffield_offCountableAgreement D hconn hconnDual hq hSheffield hagrees

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_offCountableAgreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_sheffieldNotFull_offCountableAgreement_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 ≤ q)
  (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent ≠ 1)
  (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_offCountableAgreement D hconn hconnDual hq hnotFull hagrees

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_increasingCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_sheffieldNotFull_increasingCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 ≤ q)
  (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent ≠ 1)
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountable q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_increasingCylinders D hconn hconnDual hq hnotFull hagrees

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 ≤ q)
  (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent ≠ 1)
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders D hconn hconnDual hq hnotFull hagrees

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffield_offCountable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma dualCritical_relation_of_decay_sheffield_offCountable_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent = 0)
  (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffield_offCountable D H hconn hconnDual hpc hpcDual hq hdecay hSheffield hagrees

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_offCountable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma dualCritical_relation_of_decay_sheffieldNotFull_offCountable_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent ≠ 1)
  (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_offCountable D H hconn hconnDual hpc hpcDual hq hdecay hnotFull hagrees

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_increasingCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma dualCritical_relation_of_decay_sheffieldNotFull_increasingCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent ≠ 1)
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountable q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_increasingCylinders D H hconn hconnDual hpc hpcDual hq hdecay hnotFull hagrees

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean)
-/
@[path]
private lemma dualCritical_relation_of_decay_sheffieldNotFull_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent ≠ 1)
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_logisticCylinders D H hconn hconnDual hpc hpcDual hq hdecay hnotFull hagrees


-- created on 2026-10-23
