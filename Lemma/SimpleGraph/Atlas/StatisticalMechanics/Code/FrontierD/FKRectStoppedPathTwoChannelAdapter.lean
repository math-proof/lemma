import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathTwoChannelAdapter
open SimpleGraph StatMech StatMech.FrontierD


/--
[FK.configHammingCount_le_edgeFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathTwoChannelAdapter.lean)
-/
@[path]
private lemma configHammingCount_le_edgeFinset_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega eta : ConfigSpace (Sym2 V)} :
-- imply
  FK.configHammingCount G omega eta <= G.edgeFinset.card := by
-- proof
  apply StatMech.FrontierD.FK.configHammingCount_le_edgeFinset_card G omega eta

/--
[rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathTwoChannelAdapter.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' ((rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2) := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two gamma gamma'

/--
[rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathTwoChannelAdapter.lean)
-/
@[path]
private lemma rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut_eq
  [Fintype Vout]
  [DecidableEq Vout]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {bdryOut : Vout -> Prop}
  [DecidablePred bdryOut]
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 Vout)}
  {q : Real}
  {N : Nat}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (iota : RlcConnectorVertex n -> Vout)
  (hiota : Function.Injective iota)
  (hadj : FK.ocd_AdjMatch (rlc_connectorTwoChannelGraph gamma gamma') Gout iota)
  (hwire : FK.ocd_inducedWiring Gout iota bdryOut psi = rlc_connectorSeparateWiring gamma gamma')
  (hq : 1 <= q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) <= ∑ rho : ConfigSpace (Sym2 Vout), (FK.ocd_innerRestrict iota ⁻¹' rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.condBcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q (FK.ocd_innerEdgeFinset iota) psi rho := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut hinc hstatic iota hiota hadj psi hwire hq N hscore

/--
[rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathTwoChannelAdapter.lean)
-/
@[path]
private lemma rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut_eq
  [Fintype Vout]
  [DecidableEq Vout]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {bdryOut : Vout -> Prop}
  [DecidablePred bdryOut]
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 Vout)}
  {q : Real}
  {N : Nat}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (iota : RlcConnectorVertex n -> Vout)
  (hiota : Function.Injective iota)
  (hadj : FK.ocd_AdjMatch (rlc_connectorTwoChannelGraph gamma gamma') Gout iota)
  (hwire : FK.ocd_inducedWiring Gout iota bdryOut psi = rlc_connectorSeparateWiring gamma gamma')
  (hq : 1 <= q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) * (∑ sigma ∈ FK.condFibre (FK.ocd_innerEdgeFinset iota) psi, FK.bcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q sigma) <= ∑ rho ∈ FK.condFibre (FK.ocd_innerEdgeFinset iota) psi, (FK.ocd_innerRestrict iota ⁻¹' rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator (FK.bcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q) rho := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut hinc hstatic iota hiota hadj psi hwire hq N hscore

/--
[rlc_twoChannel_condBcProb_ge_one_div_one_add_q_sq_of_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathTwoChannelAdapter.lean)
-/
@[path]
private lemma rlc_twoChannel_condBcProb_ge_one_div_one_add_q_sq_of_staticCut_eq
  [Fintype Vout]
  [DecidableEq Vout]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {bdryOut : Vout -> Prop}
  [DecidablePred bdryOut]
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 Vout)}
  {q : Real}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (iota : RlcConnectorVertex n -> Vout)
  (hiota : Function.Injective iota)
  (hadj : FK.ocd_AdjMatch (rlc_connectorTwoChannelGraph gamma gamma') Gout iota)
  (hwire : FK.ocd_inducedWiring Gout iota bdryOut psi = rlc_connectorSeparateWiring gamma gamma')
  (hq : 1 <= q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' 2) :
-- imply
  1 / (1 + q ^ 2) <= ∑ rho : ConfigSpace (Sym2 Vout), (FK.ocd_innerRestrict iota ⁻¹' rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.condBcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q (FK.ocd_innerEdgeFinset iota) psi rho := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannel_condBcProb_ge_one_div_one_add_q_sq_of_staticCut hinc hstatic iota hiota hadj psi hwire hq hscore

/--
[rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut_edgeCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathTwoChannelAdapter.lean)
-/
@[path]
private lemma rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut_edgeCard_eq
  [Fintype Vout]
  [DecidableEq Vout]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {bdryOut : Vout -> Prop}
  [DecidablePred bdryOut]
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 Vout)}
  {q : Real}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hinc.1)
  (iota : RlcConnectorVertex n -> Vout)
  (hiota : Function.Injective iota)
  (hadj : FK.ocd_AdjMatch (rlc_connectorTwoChannelGraph gamma gamma') Gout iota)
  (hwire : FK.ocd_inducedWiring Gout iota bdryOut psi = rlc_connectorSeparateWiring gamma gamma')
  (hq : 1 <= q) :
-- imply
  let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2 1 / (1 + (Real.sqrt q) ^ N * q) <= ∑ rho : ConfigSpace (Sym2 Vout), (FK.ocd_innerRestrict iota ⁻¹' rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.condBcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q (FK.ocd_innerEdgeFinset iota) psi rho := by
-- proof
  apply StatMech.FrontierD.rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut_edgeCard hinc hstatic iota hiota hadj psi hwire hq

/--
[rlc_bookFaithfulStoppedPair_condBcProb_outerFibre_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathTwoChannelAdapter.lean)
-/
@[path]
private lemma rlc_bookFaithfulStoppedPair_condBcProb_outerFibre_lower_eq
  [Fintype Vout]
  [DecidableEq Vout]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {bdryOut : Vout -> Prop}
  [DecidablePred bdryOut]
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  {psi : ConfigSpace (Sym2 Vout)}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
  {q c : Real}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hGH : rlc_connectorFiniteGraph gamma gamma' <= H)
  (hTH : rlc_connectorTraceWiring gamma gamma' <= H)
  (iota : RlcConnectorVertex n -> Vout)
  (hiota : Function.Injective iota)
  (hadj : FK.ocd_AdjMatch H Gout iota)
  (hC : FK.ocd_inducedWiring Gout iota bdryOut psi = C)
  (hq : 1 <= q)
  (hc : c <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  c * (∑ rho : ConfigSpace (Sym2 Vout), (FK.ocd_innerRestrict iota ⁻¹' rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.condBcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q (FK.ocd_innerEdgeFinset iota) psi rho) <= ∑ rho : ConfigSpace (Sym2 Vout), (FK.ocd_innerRestrict iota ⁻¹' (rlc_finiteConnectorEvent gamma gamma' ∩ rlc_finiteExtremalPairCandidate gamma gamma')).indicator (fun _ => (1 : Real)) rho * FK.condBcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q (FK.ocd_innerEdgeFinset iota) psi rho := by
-- proof
  apply StatMech.FrontierD.rlc_bookFaithfulStoppedPair_condBcProb_outerFibre_lower hfaith H hGH hTH iota hiota hadj psi C hC hq hc

/--
[rlc_bookFaithfulStoppedPair_bcProb_outerFibre_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathTwoChannelAdapter.lean)
-/
@[path]
private lemma rlc_bookFaithfulStoppedPair_bcProb_outerFibre_lower_eq
  [Fintype Vout]
  [DecidableEq Vout]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {bdryOut : Vout -> Prop}
  [DecidablePred bdryOut]
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  {psi : ConfigSpace (Sym2 Vout)}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
  {q c : Real}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hGH : rlc_connectorFiniteGraph gamma gamma' <= H)
  (hTH : rlc_connectorTraceWiring gamma gamma' <= H)
  (iota : RlcConnectorVertex n -> Vout)
  (hiota : Function.Injective iota)
  (hadj : FK.ocd_AdjMatch H Gout iota)
  (hC : FK.ocd_inducedWiring Gout iota bdryOut psi = C)
  (hq : 1 <= q)
  (hc : c <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  c * (∑ rho ∈ FK.condFibre (FK.ocd_innerEdgeFinset iota) psi, (FK.ocd_innerRestrict iota ⁻¹' rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q rho) <= ∑ rho ∈ FK.condFibre (FK.ocd_innerEdgeFinset iota) psi, (FK.ocd_innerRestrict iota ⁻¹' (rlc_finiteConnectorEvent gamma gamma' ∩ rlc_finiteExtremalPairCandidate gamma gamma')).indicator (fun _ => (1 : Real)) rho * FK.bcProb Gout (boundaryCliqueGraph bdryOut) (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.FrontierD.rlc_bookFaithfulStoppedPair_bcProb_outerFibre_lower hfaith H hGH hTH iota hiota hadj psi C hC hq hc


-- created on 2026-10-23
