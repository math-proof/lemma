/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part8
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldEndpointClosure.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.BranchAlignedOutwardEndpointCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.BranchAlignedOutwardEndpointCertificate mu) : False := by
  exact D.outwardBranchAlignedComplementary_false mu data.B data.Bpos
    data.primalArcBound data.dualArcBound data.branch
    data.a data.b data.c data.d data.xPad data.yPad
    data.vLeft data.vRight data.vBottom data.vTop
    data.hLeft data.hRight data.hBottom data.hTop
    data.vLeft_eq data.vRight_eq data.vBottom_eq data.vTop_eq
    data.hLeft_eq data.hRight_eq data.hBottom_eq data.hTop_eq
    data.xPad_ge data.yPad_ge data.outerWidth data.outerHeight
    data.primalSelected data.dualSelected


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcertificate :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.BranchAlignedOutwardEndpointCertificate mu)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  obtain ⟨data⟩ := hcertificate hcommon
  exact data.false D _


theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_branchAlignedOutwardEndpointCertificate_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.BranchAlignedOutwardEndpointCertificate mu))
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders
    hconn hconnDual hq
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate
      hp hp1 hq (hcertificate p hp hp1)
  · exact hagrees


theorem PeriodicPlanarDualPair.dualCritical_relation_of_decay_branchAlignedOutwardEndpointCertificate_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcoverage : DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
    (hcoverageDual : DualSubcriticalCoverage
      (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
    (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.BranchAlignedOutwardEndpointCertificate mu))
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  obtain ⟨hpc, hpcDual⟩ :=
    P.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one
      Pdual hq hcoverage hcoverageDual
  apply D.dualCritical_relation_of_decay_sheffieldNotFull_logisticCylinders
    H hconn hconnDual hpc hpcDual hq hdecay
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate
      hp hp1 hq (hcertificate p hp hp1)
  · exact hagrees


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcertificate :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.ExpandedEndpointSheffieldCertificate mu)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  obtain ⟨data⟩ := hcertificate hcommon
  exact data.false D _


theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_expandedEndpointCertificate_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.ExpandedEndpointSheffieldCertificate mu))
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders
    hconn hconnDual hq
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate
      hp hp1 hq (hcertificate p hp hp1)
  · exact hagrees


theorem PeriodicPlanarDualPair.dualCritical_relation_of_decay_expandedEndpointCertificate_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcoverage : DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
    (hcoverageDual : DualSubcriticalCoverage
      (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
    (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.ExpandedEndpointSheffieldCertificate mu))
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  obtain ⟨hpc, hpcDual⟩ :=
    P.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one
      Pdual hq hcoverage hcoverageDual
  apply D.dualCritical_relation_of_decay_sheffieldNotFull_logisticCylinders
    H hconn hconnDual hpc hpcDual hq hdecay
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate
      hp hp1 hq (hcertificate p hp hp1)
  · exact hagrees

end StatMech.FK.PeriodicPlanar
