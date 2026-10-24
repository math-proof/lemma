import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorMassDualityCapstone
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_connectorPIMSFailureMassTransport_of_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_connectorPIMSFailureMassTransport_of_pointwise_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hfailure : forall tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' -> rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma') :
-- imply
  RlcConnectorPIMSFailureMassTransport gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSFailureMassTransport_of_pointwise gamma gamma' hq hfailure

/--
[rlc_connectorPIMSCollaredFailureMassTransport_of_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredFailureMassTransport_of_pointwise_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hfailure : forall tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' -> rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma') :
-- imply
  RlcConnectorPIMSCollaredFailureMassTransport gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredFailureMassTransport_of_pointwise gamma gamma' hq hfailure

/--
[rlc_connectorPIMSFailureMassTransport_of_boundaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_connectorPIMSFailureMassTransport_of_boundaryArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (harc : forall tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' -> RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
-- imply
  RlcConnectorPIMSFailureMassTransport gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSFailureMassTransport_of_boundaryArc gamma gamma' hq harc

/--
[rlc_connectorPIMSFailureMassTransport_of_contourCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_connectorPIMSFailureMassTransport_of_contourCertificate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hcontour : forall tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' -> RlcConnectorPIMSContourCertificate gamma gamma' tau) :
-- imply
  RlcConnectorPIMSFailureMassTransport gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSFailureMassTransport_of_contourCertificate gamma gamma' hq hcontour

/--
[rlc_connectorPIMSCollaredFailureMassTransport_of_reflectedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredFailureMassTransport_of_reflectedDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hfailure : forall tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' -> rlc_connectorReflectedDualConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma') :
-- imply
  RlcConnectorPIMSCollaredFailureMassTransport gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredFailureMassTransport_of_reflectedDual gamma gamma' hq hfailure

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_inducedWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_inducedWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
-- given
  (hq : 1 <= q)
  (hC : C <= rlc_connectorMergedWiring gamma gamma')
  (htransport : RlcConnectorPIMSFailureMassTransport gamma gamma' q)
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') C (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_inducedWiring gamma gamma' hq C hC htransport hpush

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_inducedMixture_eq
  {n : Int}
  [Fintype I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  [forall i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (w : I -> Real)
  (C : I -> SimpleGraph (RlcConnectorVertex n))
  (hw : forall i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
  (htransport : RlcConnectorPIMSFailureMassTransport gamma gamma' q)
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i) (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_inducedMixture gamma gamma' hq w C hw hwSum hC htransport hpush

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_weightedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_weightedMixture_eq
  {n : Int}
  [Fintype I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  [forall i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (w : I -> Real)
  (C : I -> SimpleGraph (RlcConnectorVertex n))
  (pf : I -> Sym2 (RlcConnectorVertex n) -> Real)
  (hw : forall i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
  (hpf0 : forall i e, 0 <= pf i e)
  (hpf1 : forall i e, pf i e < 1)
  (hpfle : forall i e, pf i e <= BeffaraDC.selfDualPoint q)
  (htransport : RlcConnectorPIMSFailureMassTransport gamma gamma' q)
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * (∑ omega, (rlc_finiteConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) omega * FK.bcProbW (rlc_connectorFiniteGraph gamma gamma') (C i) (pf i) q omega)) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_weightedMixture gamma gamma' hq w C pf hw hwSum hC hpf0 hpf1 hpfle htransport hpush

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollaredFailureMass_componentMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollaredFailureMass_componentMixture_eq
  {n : Int}
  [Fintype I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (w : I -> Real)
  (tauExt : I -> ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (hw : forall i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (htransport : RlcConnectorPIMSCollaredFailureMassTransport gamma gamma' q)
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * (∑ omega, (rlc_finiteConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) omega * FK.bcProbW (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorComponentWiring (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' (tauExt i))) (rlc_connectorPIMSCollaredParameter gamma gamma' (BeffaraDC.selfDualPoint q)) q omega)) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollaredFailureMass_componentMixture gamma gamma' hq w tauExt hw hwSum htransport hpush


-- created on 2026-10-23
