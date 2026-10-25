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
import Def.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding.Part5
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

theorem fkRectWindingStoppedRectangleEmbedding_injective
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    Function.Injective
      (fkRectWindingStoppedRectangleEmbedding
        k scale blocks hwidth hblocks) :=
  fkRectStoppedPathFullRectangleEmbedding_injective
    (fkRectWindingBlockVerticalFamily k scale blocks)
    (fkRectWindingStoppedRectangleCenter
      k scale blocks hwidth hblocks)
    scale 1 1
    ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)
    (fkRectWindingStoppedRectangle_fits
      k scale blocks hwidth hblocks)

theorem fkRectWindingStoppedRectangleEmbedding_adjMatch
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale)
      (fkRectTorusGraph
        (fkRectWindingBlockVerticalFamily k scale blocks))
      (fkRectWindingStoppedRectangleEmbedding
        k scale blocks hwidth hblocks) :=
  fkRectStoppedPathFullRectangleEmbedding_adjMatch
    (fkRectWindingBlockVerticalFamily k scale blocks)
    (fkRectWindingStoppedRectangleCenter
      k scale blocks hwidth hblocks)
    scale 1 1
    ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)
    (by omega) (by omega)
    (fkRectWindingStoppedRectangle_fits
      k scale blocks hwidth hblocks)


theorem fkRectWinding_bookFaithfulStoppedPair_fibre_lower
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks)
    (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (psi : ConfigSpace (Sym2
      (fkRectWindingBlockVerticalFamily k scale blocks).Vertex))
    (C : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel C.Adj]
    (hC : FK.ocd_inducedWiring
      (fkRectTorusGraph
        (fkRectWindingBlockVerticalFamily k scale blocks))
      (fkRectWindingStoppedRectangleEmbedding
        k scale blocks hwidth hblocks)
      (fun _ => False) psi = C)
    {q c : Real} (hq : 1 <= q)
    (hc : c <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent gamma gamma')) :
    let iota := fkRectWindingStoppedRectangleEmbedding
      k scale blocks hwidth hblocks
    let G := fkRectTorusGraph
      (fkRectWindingBlockVerticalFamily k scale blocks)
    let F := FK.ocd_innerEdgeFinset iota
    c *
        (∑ rho ∈ FK.condFibre F psi,
          (FK.ocd_innerRestrict iota ⁻¹'
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.fkProb G (fkRectCriticalP q) q rho) <=
      ∑ rho ∈ FK.condFibre F psi,
        (FK.ocd_innerRestrict iota ⁻¹'
          (rlc_finiteConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma')).indicator
              (fun _ => (1 : Real)) rho *
          FK.fkProb G (fkRectCriticalP q) q rho := by
  classical
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  let iota := fkRectWindingStoppedRectangleEmbedding
    k scale blocks hwidth hblocks
  let G := fkRectTorusGraph R
  have hraw := rlc_bookFaithfulStoppedPair_bcProb_outerFibre_lower
    (Gout := G) (bdryOut := fun _ : R.Vertex => False)
    hfaith (rlcConnectorFullRectangleGraph scale)
    (rlc_connectorFiniteGraph_le_fullRectangle scale gamma gamma')
    (rlc_connectorTraceWiring_le_fullRectangle scale gamma gamma')
    iota
    (fkRectWindingStoppedRectangleEmbedding_injective
      k scale blocks hwidth hblocks)
    (fkRectWindingStoppedRectangleEmbedding_adjMatch
      k scale blocks hwidth hblocks)
    psi C hC hq hc
  have hboundary : boundaryCliqueGraph (fun _ : R.Vertex => False) =
      (⊥ : SimpleGraph R.Vertex) := by
    apply SimpleGraph.ext
    ext x y
    rw [boundaryCliqueGraph_adj]
    simp [SimpleGraph.bot_adj]
  dsimp only
  simpa only [R, iota, G, hboundary, FK.bcProb_bot_eq_fkProb,
    fkRectCriticalP, BeffaraDC.selfDualPoint] using hraw


theorem fkRectWinding_bookFaithfulStoppedPair_fibre_qsq_lower
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks)
    (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (psi : ConfigSpace (Sym2
      (fkRectWindingBlockVerticalFamily k scale blocks).Vertex))
    (C : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel C.Adj]
    (hC : FK.ocd_inducedWiring
      (fkRectTorusGraph
        (fkRectWindingBlockVerticalFamily k scale blocks))
      (fkRectWindingStoppedRectangleEmbedding
        k scale blocks hwidth hblocks)
      (fun _ => False) psi = C)
    {q : Real} (hq : 1 <= q)
    (hlocal : 1 / (1 + q ^ 2) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma')) :
    let iota := fkRectWindingStoppedRectangleEmbedding
      k scale blocks hwidth hblocks
    let G := fkRectTorusGraph
      (fkRectWindingBlockVerticalFamily k scale blocks)
    let F := FK.ocd_innerEdgeFinset iota
    1 / (1 + q ^ 2) *
        (∑ rho ∈ FK.condFibre F psi,
          (FK.ocd_innerRestrict iota ⁻¹'
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.fkProb G (fkRectCriticalP q) q rho) <=
      ∑ rho ∈ FK.condFibre F psi,
        (FK.ocd_innerRestrict iota ⁻¹'
          (rlc_finiteConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma')).indicator
              (fun _ => (1 : Real)) rho *
          FK.fkProb G (fkRectCriticalP q) q rho := by
  exact fkRectWinding_bookFaithfulStoppedPair_fibre_lower
    k scale blocks hwidth hblocks gamma gamma' hfaith psi C hC hq hlocal

end
end StatMech.FrontierD
