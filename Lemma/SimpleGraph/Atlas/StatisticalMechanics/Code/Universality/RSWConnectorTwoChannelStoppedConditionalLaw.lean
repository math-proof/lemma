import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelActiveEvent_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_twoChannelActiveEvent_preimage_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  FK.restrictActive (rlc_connectorTwoChannelGraph gamma gamma') ⁻¹' rlc_twoChannelActiveEvent gamma gamma' = rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelActiveEvent_preimage gamma gamma'

/--
[RlcTwoChannelCompatibleExteriorFibre.trace_le_frozenExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma trace_le_frozenExterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi}
  {B : SimpleGraph (RlcConnectorVertex n)} :
-- imply
  rlc_connectorTraceWiring gamma gamma' ≤ FK.edgeSubsetFrozenExteriorGraph (rlc_connectorTwoChannelGraph gamma gamma') H B psi := by
-- proof
  apply StatMech.Universality.RlcTwoChannelCompatibleExteriorFibre.trace_le_frozenExterior F B

/--
[RlcTwoChannelCompatibleExteriorFibre.separate_le_inducedWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma separate_le_inducedWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi}
  {B : SimpleGraph (RlcConnectorVertex n)} :
-- imply
  rlc_connectorSeparateWiring gamma gamma' ≤ FK.edgeSubsetInducedWiring (rlc_connectorTwoChannelGraph gamma gamma') H B psi := by
-- proof
  apply StatMech.Universality.RlcTwoChannelCompatibleExteriorFibre.separate_le_inducedWiring F B

/--
[rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_separate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') ≤ FK.edgeSubsetFibreCondEventMass (rlc_connectorTwoChannelGraph gamma gamma') H B psi (BeffaraDC.selfDualPoint q) q (rlc_twoChannelActiveEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_separate gamma gamma' H B psi F hq

/--
[rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_of_retainedAnchor_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi}
  {q : Real}
  {N : Nat}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 ≤ q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) ≤ FK.edgeSubsetFibreCondEventMass (rlc_connectorTwoChannelGraph gamma gamma') H B psi (BeffaraDC.selfDualPoint q) q (rlc_twoChannelActiveEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_of_retainedAnchor_staticCut H B psi F hinc hstatic hq N hscore

/--
[rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi}
  {q : Real}
  {N : Nat}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 ≤ q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) * (∑ rho ∈ FK.condFibre (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi, FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho ∈ FK.condFibre (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi, (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut H B psi F hinc hstatic hq N hscore

/--
[rlc_twoChannelOutsideEventMass_lower_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_twoChannelOutsideEventMass_lower_of_retainedAnchor_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {S : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
  {q : Real}
  {N : Nat}
-- given
  (hS : FK.DependsOnOutside (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset S)
  (hcompat : ∀ {psi}, psi ∈ S → RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi)
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 ≤ q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) * (∑ rho, S.indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho, (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ S).indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannelOutsideEventMass_lower_of_retainedAnchor_staticCut gamma gamma' H B S hS hcompat hinc hstatic hq N hscore

/--
[rlc_finiteExtremalPairCandidate_dependsOnOutside_twoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_dependsOnOutside_twoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma') (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset) :
-- imply
  FK.DependsOnOutside (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset (rlc_finiteExtremalPairCandidate gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidate_dependsOnOutside_twoChannel gamma gamma' hdisj

/--
[rlc_finiteExtremalPairCandidate_twoChannelMass_lower_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_twoChannelMass_lower_of_retainedAnchor_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {q : Real}
  {N : Nat}
-- given
  (hKH : rlc_connectorTwoChannelGraph gamma gamma' ≤ H)
  (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
  (hdisj : Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma') (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset)
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 ≤ q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) * (∑ rho, (rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho, (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidate_twoChannelMass_lower_of_retainedAnchor_staticCut gamma gamma' H B hKH hTH hdisj hinc hstatic hq N hscore


-- created on 2026-10-23
