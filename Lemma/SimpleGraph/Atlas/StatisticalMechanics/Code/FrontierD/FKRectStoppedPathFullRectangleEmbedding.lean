import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding.Part5
open SimpleGraph StatMech StatMech.FrontierD


/--
[rlc_connectorFiniteGraph_le_fullRectangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_connectorFiniteGraph_le_fullRectangle_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)} :
-- imply
  rlc_connectorFiniteGraph gamma gamma' <= rlcConnectorFullRectangleGraph scale := by
-- proof
  apply StatMech.FrontierD.rlc_connectorFiniteGraph_le_fullRectangle scale gamma gamma'

/--
[rlc_connectorTraceWiring_le_fullRectangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_connectorTraceWiring_le_fullRectangle_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)} :
-- imply
  rlc_connectorTraceWiring gamma gamma' <= rlcConnectorFullRectangleGraph scale := by
-- proof
  apply StatMech.FrontierD.rlc_connectorTraceWiring_le_fullRectangle scale gamma gamma'

/--
[rlc_connectorTwoChannelGraph_le_fullRectangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_connectorTwoChannelGraph_le_fullRectangle_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)} :
-- imply
  rlc_connectorTwoChannelGraph gamma gamma' <= rlcConnectorFullRectangleGraph scale := by
-- proof
  apply StatMech.FrontierD.rlc_connectorTwoChannelGraph_le_fullRectangle scale gamma gamma'

/--
[rlc_twoChannelCompatibleExteriorFibre_fullRectangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_twoChannelCompatibleExteriorFibre_fullRectangle_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int)))}
-- given
  (htrace : ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true) :
-- imply
  RlcTwoChannelCompatibleExteriorFibre gamma gamma' (rlcConnectorFullRectangleGraph scale) psi := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannelCompatibleExteriorFibre_fullRectangle scale gamma gamma' psi htrace

/--
[rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)}
  {B : SimpleGraph (RlcConnectorVertex (scale : Int))}
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int)))}
  {q : Real}
  {N : Nat}
-- given
  (htrace : ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 <= q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) * (∑ rho ∈ FK.condFibre (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi, FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho) <= ∑ rho ∈ FK.condFibre (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi, (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut scale gamma gamma' B psi htrace hinc hstatic hq N hscore

/--
[rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut_edgeCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut_edgeCard_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)}
  {B : SimpleGraph (RlcConnectorVertex (scale : Int))}
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int)))}
  {q : Real}
-- given
  (htrace : ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 <= q) :
-- imply
  let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2 1 / (1 + (Real.sqrt q) ^ N * q) * (∑ rho ∈ FK.condFibre (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi, FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho) <= ∑ rho ∈ FK.condFibre (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi, (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut_edgeCard scale gamma gamma' B psi htrace hinc hstatic hq

/--
[rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)}
  {B : SimpleGraph (RlcConnectorVertex (scale : Int))}
  [DecidableRel B.Adj]
  {S : Set (ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int))))}
  {q : Real}
  {N : Nat}
-- given
  (hS : FK.DependsOnOutside (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset S)
  (htrace : ∀ {psi}, psi ∈ S → ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 <= q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) * (∑ rho, S.indicator (fun _ => (1 : Real)) rho * FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho) <= ∑ rho, (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ S).indicator (fun _ => (1 : Real)) rho * FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut scale gamma gamma' B S hS htrace hinc hstatic hq N hscore

/--
[rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut_edgeCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut_edgeCard_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)}
  {B : SimpleGraph (RlcConnectorVertex (scale : Int))}
  [DecidableRel B.Adj]
  {S : Set (ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int))))}
  {q : Real}
-- given
  (hS : FK.DependsOnOutside (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset S)
  (htrace : ∀ {psi}, psi ∈ S → ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 <= q) :
-- imply
  let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2 1 / (1 + (Real.sqrt q) ^ N * q) * (∑ rho, S.indicator (fun _ => (1 : Real)) rho * FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho) <= ∑ rho, (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ S).indicator (fun _ => (1 : Real)) rho * FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut_edgeCard scale gamma gamma' B S hS htrace hinc hstatic hq

/--
[rlc_finiteExtremalPairCandidate_fullRectangle_twoChannelMass_lower_edgeCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_fullRectangle_twoChannelMass_lower_edgeCard_eq
  {scale : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)}
  {B : SimpleGraph (RlcConnectorVertex (scale : Int))}
  [DecidableRel B.Adj]
  {q : Real}
-- given
  (hdisj : Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma') (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset)
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (hq : 1 <= q) :
-- imply
  let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2 1 / (1 + (Real.sqrt q) ^ N * q) * (∑ rho, (rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho) <= ∑ rho, (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb (rlcConnectorFullRectangleGraph scale) B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.FrontierD.rlc_finiteExtremalPairCandidate_fullRectangle_twoChannelMass_lower_edgeCard scale gamma gamma' B hdisj hinc hstatic hq

/--
[rlcConnectorFullRectangleBoxInclusion_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlcConnectorFullRectangleBoxInclusion_injective_eq
  {scale : Nat} :
-- imply
  Function.Injective (rlcConnectorFullRectangleBoxInclusion scale) := by
-- proof
  apply StatMech.FrontierD.rlcConnectorFullRectangleBoxInclusion_injective scale

/--
[rlcConnectorFullRectangleBoxInclusion_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma rlcConnectorFullRectangleBoxInclusion_adjMatch_eq
  {scale : Nat} :
-- imply
  FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale) (FK.boxGraph 2 (2 * scale)) (rlcConnectorFullRectangleBoxInclusion scale) := by
-- proof
  apply StatMech.FrontierD.rlcConnectorFullRectangleBoxInclusion_adjMatch scale

/--
[fkRectStoppedPathFullRectangleEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma fkRectStoppedPathFullRectangleEmbedding_injective_eq
  {R : FKRectTorus}
  {center : R.Vertex}
  {scale cut lower upper : Nat}
-- given
  (hfit : FKRectLocalBoxFits R center (2 * scale) cut lower upper) :
-- imply
  Function.Injective (fkRectStoppedPathFullRectangleEmbedding R center scale cut lower upper hfit) := by
-- proof
  apply StatMech.FrontierD.fkRectStoppedPathFullRectangleEmbedding_injective R center scale cut lower upper hfit

/--
[fkRectStoppedPathFullRectangleEmbedding_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma fkRectStoppedPathFullRectangleEmbedding_adjMatch_eq
  {R : FKRectTorus}
  {center : R.Vertex}
  {scale cut lower upper : Nat}
-- given
  (hcut : 1 <= cut)
  (hlower : 1 <= lower)
  (hfit : FKRectLocalBoxFits R center (2 * scale) cut lower upper) :
-- imply
  FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale) (fkRectTorusGraph R) (fkRectStoppedPathFullRectangleEmbedding R center scale cut lower upper hfit) := by
-- proof
  apply StatMech.FrontierD.fkRectStoppedPathFullRectangleEmbedding_adjMatch R center scale cut lower upper hcut hlower hfit

/--
[fkRectWindingStoppedRectangle_fits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma fkRectWindingStoppedRectangle_fits_eq
  {k scale blocks : Nat}
-- given
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hblocks : 3 <= blocks) :
-- imply
  FKRectLocalBoxFits (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectWindingStoppedRectangleCenter k scale blocks hwidth hblocks) (2 * scale) 1 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingStoppedRectangle_fits k scale blocks hwidth hblocks

/--
[fkRectWindingStoppedRectangleEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma fkRectWindingStoppedRectangleEmbedding_injective_eq
  {k scale blocks : Nat}
-- given
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hblocks : 3 <= blocks) :
-- imply
  Function.Injective (fkRectWindingStoppedRectangleEmbedding k scale blocks hwidth hblocks) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingStoppedRectangleEmbedding_injective k scale blocks hwidth hblocks

/--
[fkRectWindingStoppedRectangleEmbedding_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma fkRectWindingStoppedRectangleEmbedding_adjMatch_eq
  {k scale blocks : Nat}
-- given
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hblocks : 3 <= blocks) :
-- imply
  FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale) (fkRectTorusGraph (fkRectWindingBlockVerticalFamily k scale blocks)) (fkRectWindingStoppedRectangleEmbedding k scale blocks hwidth hblocks) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingStoppedRectangleEmbedding_adjMatch k scale blocks hwidth hblocks

/--
[fkRectWinding_bookFaithfulStoppedPair_fibre_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma fkRectWinding_bookFaithfulStoppedPair_fibre_lower_eq
  {k scale blocks : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)}
  {psi : ConfigSpace (Sym2 (fkRectWindingBlockVerticalFamily k scale blocks).Vertex)}
  {C : SimpleGraph (RlcConnectorVertex (scale : Int))}
  [DecidableRel C.Adj]
  {q c : Real}
-- given
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hblocks : 3 <= blocks)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hC : FK.ocd_inducedWiring (fkRectTorusGraph (fkRectWindingBlockVerticalFamily k scale blocks)) (fkRectWindingStoppedRectangleEmbedding k scale blocks hwidth hblocks) (fun _ => False) psi = C)
  (hq : 1 <= q)
  (hc : c <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  let iota := fkRectWindingStoppedRectangleEmbedding k scale blocks hwidth hblocks let G := fkRectTorusGraph (fkRectWindingBlockVerticalFamily k scale blocks) let F := FK.ocd_innerEdgeFinset iota c * (∑ rho ∈ FK.condFibre F psi, (FK.ocd_innerRestrict iota ⁻¹' rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.fkProb G (fkRectCriticalP q) q rho) <= ∑ rho ∈ FK.condFibre F psi, (FK.ocd_innerRestrict iota ⁻¹' (rlc_finiteConnectorEvent gamma gamma' ∩ rlc_finiteExtremalPairCandidate gamma gamma')).indicator (fun _ => (1 : Real)) rho * FK.fkProb G (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectWinding_bookFaithfulStoppedPair_fibre_lower k scale blocks hwidth hblocks gamma gamma' hfaith psi C hC hq hc

/--
[fkRectWinding_bookFaithfulStoppedPair_fibre_qsq_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean)
-/
@[path]
private lemma fkRectWinding_bookFaithfulStoppedPair_fibre_qsq_lower_eq
  {k scale blocks : Nat}
  {gamma : RlcRightDiagonalPath (scale : Int)}
  {gamma' : RlcLeftDiagonalPath (scale : Int)}
  {psi : ConfigSpace (Sym2 (fkRectWindingBlockVerticalFamily k scale blocks).Vertex)}
  {C : SimpleGraph (RlcConnectorVertex (scale : Int))}
  [DecidableRel C.Adj]
  {q : Real}
-- given
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hblocks : 3 <= blocks)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hC : FK.ocd_inducedWiring (fkRectTorusGraph (fkRectWindingBlockVerticalFamily k scale blocks)) (fkRectWindingStoppedRectangleEmbedding k scale blocks hwidth hblocks) (fun _ => False) psi = C)
  (hq : 1 <= q)
  (hlocal : 1 / (1 + q ^ 2) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  let iota := fkRectWindingStoppedRectangleEmbedding k scale blocks hwidth hblocks let G := fkRectTorusGraph (fkRectWindingBlockVerticalFamily k scale blocks) let F := FK.ocd_innerEdgeFinset iota 1 / (1 + q ^ 2) * (∑ rho ∈ FK.condFibre F psi, (FK.ocd_innerRestrict iota ⁻¹' rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.fkProb G (fkRectCriticalP q) q rho) <= ∑ rho ∈ FK.condFibre F psi, (FK.ocd_innerRestrict iota ⁻¹' (rlc_finiteConnectorEvent gamma gamma' ∩ rlc_finiteExtremalPairCandidate gamma gamma')).indicator (fun _ => (1 : Real)) rho * FK.fkProb G (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectWinding_bookFaithfulStoppedPair_fibre_qsq_lower k scale blocks hwidth hblocks gamma gamma' hfaith psi C hC hq hlocal


-- created on 2026-10-23
