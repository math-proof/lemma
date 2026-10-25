import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part3
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_maskConfig_axisGapAmbientConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_maskConfig_axisGapAmbientConfig_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_maskConfig (rlc_axisGapEdges G) (rlc_axisGapAmbientConfig G tau) = rlc_axisGapAmbientConfig G tau := by
-- proof
  apply StatMech.Universality.rlc_maskConfig_axisGapAmbientConfig G tau

/--
[rlc_axisGapPIMSReflectedConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSReflectedConfig_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau f = !(rlc_axisGapAmbientConfig G tau (rlc_pimsEdgeEquiv (f.map Subtype.val))) := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSReflectedConfig_apply G tau f

/--
[rlc_axisGapPIMSSourceOpenCase_of_maskedDual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSSourceOpenCase_of_maskedDual_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (hopen : rlc_dualReflectConfig (rlc_maskConfig (rlc_axisGapEdges G) (rlc_axisGapAmbientConfig G tau)) e = true) :
-- imply
  RlcAxisGapPIMSSourceOpenCase G tau e := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSSourceOpenCase_of_maskedDual_open G tau e hopen

/--
[rlc_axisGapPIMSReflectedConfig_open_of_sourceOpenCase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSReflectedConfig_open_of_sourceOpenCase_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (htarget : e ∈ rlc_axisGapEdges G)
  (hcase : RlcAxisGapPIMSSourceOpenCase G tau e) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau (rlc_axisGapEdgeLift G e htarget) = true := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSReflectedConfig_open_of_sourceOpenCase G tau e htarget hcase

/--
[rlc_axisGapPIMSReflectedConfig_open_of_finite_sourceOpenCase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSReflectedConfig_open_of_finite_sourceOpenCase_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (hcase : RlcAxisGapPIMSSourceOpenCase G tau (e.map Subtype.val)) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau e = true := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSReflectedConfig_open_of_finite_sourceOpenCase G tau e hcase

/--
[rlc_axisGapEdge_endpoint_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapEdge_endpoint_mem_box_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_axisGapEdges G)
  (hz : z ∈ e) :
-- imply
  z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdge_endpoint_mem_box G he hz

/--
[rlc_walk_support_mem_connectorBox_of_axisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_walk_support_mem_connectorBox_of_axisGapEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {H : SimpleGraph (Site 2)}
  {x y : Site 2}
  {a : H.Walk x y}
-- given
  (hy : y ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
  (hedges : ∀ e ∈ a.edges, e ∈ rlc_axisGapEdges G) :
-- imply
  ∀ z ∈ a.support, z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_walk_support_mem_connectorBox_of_axisGapEdges G a hy hedges

/--
[rlc_axisGapPIMSActualSelectedArc_of_boundaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSActualSelectedArc_of_boundaryArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (harc : RlcAxisGapPIMSBoundaryArc G hn hlt tau) :
-- imply
  RlcAxisGapPIMSActualSelectedArc G tau := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSActualSelectedArc_of_boundaryArc G hn hlt tau harc

/--
[rlc_axisGapPIMS_openWalk_of_actualSelectedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMS_openWalk_of_actualSelectedArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : Site 2}
  {c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_maskConfig (rlc_axisGapEdges G) (rlc_axisGapAmbientConfig G tau)))).Walk x y}
-- given
  (hsupport : ∀ z ∈ c.support, z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
  (htarget : ∀ e ∈ c.edges, e ∈ rlc_axisGapEdges G)
  (hsource : ∀ e ∈ c.edges, RlcAxisGapPIMSSourceOpenCase G tau e) :
-- imply
  Nonempty ((FK.openSub (rlc_axisGapFiniteGraph G) (rlc_axisGapPIMSReflectedConfig G tau)).Walk ⟨x, hsupport x c.start_mem_support⟩ ⟨y, hsupport y c.end_mem_support⟩) := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMS_openWalk_of_actualSelectedArc G tau c hsupport htarget hsource

/--
[rlc_axisGapPIMSReflectedConfig_mem_event_of_actualSelectedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSReflectedConfig_mem_event_of_actualSelectedArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (harc : RlcAxisGapPIMSActualSelectedArc G tau) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSReflectedConfig_mem_event_of_actualSelectedArc G tau harc

/--
[rlc_axisGapPIMSReflectedConfig_mem_event_of_boundaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSReflectedConfig_mem_event_of_boundaryArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (harc : RlcAxisGapPIMSBoundaryArc G hn hlt tau) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSReflectedConfig_mem_event_of_boundaryArc G hn hlt tau harc


-- created on 2026-10-23
