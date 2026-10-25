/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathTwoChannelAdapter
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw.Part2
import Instance.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

theorem rlc_connectorFiniteGraph_le_fullRectangle
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int)) :
    rlc_connectorFiniteGraph gamma gamma' <=
      rlcConnectorFullRectangleGraph scale := by
  intro x y hxy
  exact hxy.1


theorem rlc_connectorTraceWiring_le_fullRectangle
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int)) :
    rlc_connectorTraceWiring gamma gamma' <=
      rlcConnectorFullRectangleGraph scale := by
  intro x y hxy
  exact hxy.1


theorem rlc_connectorTwoChannelGraph_le_fullRectangle
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int)) :
    rlc_connectorTwoChannelGraph gamma gamma' <=
      rlcConnectorFullRectangleGraph scale := by
  intro x y hxy
  exact hxy.1.elim (fun hcentral => hcentral.1)
    (fun hreflected => hreflected.1)


theorem rlc_twoChannelCompatibleExteriorFibre_fullRectangle
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int))))
    (htrace : ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true) :
    RlcTwoChannelCompatibleExteriorFibre gamma gamma'
      (rlcConnectorFullRectangleGraph scale) psi := by
  exact
    { twoChannel_le :=
        rlc_connectorTwoChannelGraph_le_fullRectangle scale gamma gamma'
      trace_le :=
        rlc_connectorTraceWiring_le_fullRectangle scale gamma gamma'
      trace_open := htrace }


theorem
    rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int))))
    (htrace : ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho ∈ FK.condFibre
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho ∈ FK.condFibre
        (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  exact
    StatMech.Universality.rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut
      (rlcConnectorFullRectangleGraph scale) B psi
      (rlc_twoChannelCompatibleExteriorFibre_fullRectangle
        scale gamma gamma' psi htrace)
      hinc hstatic hq N hscore


theorem
    rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut_edgeCard
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int))))
    (htrace : ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) :
    let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho ∈ FK.condFibre
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho ∈ FK.condFibre
        (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  dsimp only
  exact
    rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut
      scale gamma gamma' B psi htrace hinc hstatic hq _
        (rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two
          gamma gamma')


theorem
    rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (S : Set (ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int)))))
    (hS : FK.DependsOnOutside
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset S)
    (htrace : ∀ {psi}, psi ∈ S → ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ S).indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  exact
    StatMech.Universality.rlc_twoChannelOutsideEventMass_lower_of_retainedAnchor_staticCut
      gamma gamma' (rlcConnectorFullRectangleGraph scale) B S hS
      (fun {psi} hpsi =>
        rlc_twoChannelCompatibleExteriorFibre_fullRectangle
          scale gamma gamma' psi (htrace hpsi))
      hinc hstatic hq N hscore


theorem
    rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut_edgeCard
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (S : Set (ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int)))))
    (hS : FK.DependsOnOutside
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset S)
    (htrace : ∀ {psi}, psi ∈ S → ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) :
    let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ S).indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  dsimp only
  exact
    rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut
      scale gamma gamma' B S hS htrace hinc hstatic hq _
        (rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two
          gamma gamma')


theorem
    rlc_finiteExtremalPairCandidate_fullRectangle_twoChannelMass_lower_edgeCard
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (hdisj : Disjoint
      (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) :
    let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho,
          (rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.bcProb (rlcConnectorFullRectangleGraph scale) B
              (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  dsimp only
  exact
    rlc_finiteExtremalPairCandidate_twoChannelMass_lower_of_retainedAnchor_staticCut
      gamma gamma' (rlcConnectorFullRectangleGraph scale) B
      (rlc_connectorTwoChannelGraph_le_fullRectangle scale gamma gamma')
      (rlc_connectorTraceWiring_le_fullRectangle scale gamma gamma')
      hdisj hinc hstatic hq _
        (rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two
          gamma gamma')


end
end StatMech.FrontierD
