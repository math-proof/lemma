import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part3
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_axisGapPIMSAnchoredContourCore_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSAnchoredContourCore_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  Nonempty (RlcAxisGapPIMSAnchoredContourCore G tau) := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSAnchoredContourCore_of_failure G tau hno

/--
[rlc_axisGapPIMSBoundaryArc_of_anchoredSelectedSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSBoundaryArc_of_anchoredSelectedSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {C : RlcAxisGapPIMSAnchoredContourCore G tau}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hside : RlcAxisGapPIMSAnchoredSelectedSide G hn hlt tau C) :
-- imply
  RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSBoundaryArc_of_anchoredSelectedSide G hn hlt tau hside

/--
[rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hside : RlcAxisGapPIMSAnchoredSideExists G hn hlt tau) :
-- imply
  RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists G hn hlt tau hside

/--
[rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hselector : RlcAxisGapPIMSAnchoredContourSelector G hn hlt) :
-- imply
  RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector G hn hlt hselector

/--
[rlc_axisGapPIMS_success_of_failureSelectedSideTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMS_success_of_failureSelectedSideTopology_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (htopology : RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt)
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMS_success_of_failureSelectedSideTopology G hn hlt htopology tau hno

/--
[rlc_axisGapPIMS_success_of_anchoredContourSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean)
-/
@[path]
private lemma rlc_axisGapPIMS_success_of_anchoredContourSelector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hselector : RlcAxisGapPIMSAnchoredContourSelector G hn hlt)
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMS_success_of_anchoredContourSelector G hn hlt hselector tau hno


-- created on 2026-10-23
