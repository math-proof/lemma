import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldEndpointClosure
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlanarDualPair.ExpandedEndpointSheffieldCertificate.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean)
-/
@[path]
private lemma false_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : D.ExpandedEndpointSheffieldCertificate mu} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.ExpandedEndpointSheffieldCertificate.false D mu data

/--
[PeriodicPlanarDualPair.BranchAlignedOutwardEndpointCertificate.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean)
-/
@[path]
private lemma false_eq_2
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : D.BranchAlignedOutwardEndpointCertificate mu} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.BranchAlignedOutwardEndpointCertificate.false D mu data

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hcertificate : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> Nonempty (D.BranchAlignedOutwardEndpointCertificate mu)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate D hp hp1 hq hcertificate

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_branchAlignedOutwardEndpointCertificate_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_branchAlignedOutwardEndpointCertificate_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 <= q)
  (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> Nonempty (D.BranchAlignedOutwardEndpointCertificate mu))
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_branchAlignedOutwardEndpointCertificate_logisticCylinders D hconn hconnDual hq hcertificate hagrees

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_decay_branchAlignedOutwardEndpointCertificate_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean)
-/
@[path]
private lemma dualCritical_relation_of_decay_branchAlignedOutwardEndpointCertificate_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 <= q)
  (hcoverage : DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
  (hcoverageDual : DualSubcriticalCoverage (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> Nonempty (D.BranchAlignedOutwardEndpointCertificate mu))
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_decay_branchAlignedOutwardEndpointCertificate_logisticCylinders D H hconn hconnDual hq hcoverage hcoverageDual hdecay hcertificate hagrees

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hcertificate : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> Nonempty (D.ExpandedEndpointSheffieldCertificate mu)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate D hp hp1 hq hcertificate

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_expandedEndpointCertificate_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_expandedEndpointCertificate_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 <= q)
  (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> Nonempty (D.ExpandedEndpointSheffieldCertificate mu))
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_expandedEndpointCertificate_logisticCylinders D hconn hconnDual hq hcertificate hagrees

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_decay_expandedEndpointCertificate_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean)
-/
@[path]
private lemma dualCritical_relation_of_decay_expandedEndpointCertificate_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 <= q)
  (hcoverage : DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
  (hcoverageDual : DualSubcriticalCoverage (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> Nonempty (D.ExpandedEndpointSheffieldCertificate mu))
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_decay_expandedEndpointCertificate_logisticCylinders D H hconn hconnDual hq hcoverage hcoverageDual hdecay hcertificate hagrees


-- created on 2026-10-23
