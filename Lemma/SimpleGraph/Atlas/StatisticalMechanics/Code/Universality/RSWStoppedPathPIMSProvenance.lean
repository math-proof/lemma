import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part3
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_extremalPairCandidateEdges_subset_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma rlc_extremalPairCandidateEdges_subset_explored_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_extremalPairCandidateEdges (gamma, gamma') ⊆ StatMech.Percolation.edgesWithinFinset (rlc_rightExploredVertices gamma) ∪ StatMech.Percolation.edgesWithinFinset (rlc_leftExploredVertices gamma') := by
-- proof
  apply StatMech.Universality.rlc_extremalPairCandidateEdges_subset_explored gamma gamma'

/--
[rlc_sequentialExtremalClosedComparison_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma rlc_sequentialExtremalClosedComparison_of_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_sequentialExtremalExteriorEdges gamma gamma') :
-- imply
  rlc_sequentialExtremalClosedComparison gamma gamma' omega e = false := by
-- proof
  apply StatMech.Universality.rlc_sequentialExtremalClosedComparison_of_mem omega he

/--
[rlc_sequentialExtremalClosedComparison_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma rlc_sequentialExtremalClosedComparison_of_not_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∉ rlc_sequentialExtremalExteriorEdges gamma gamma') :
-- imply
  rlc_sequentialExtremalClosedComparison gamma gamma' omega e = omega e := by
-- proof
  apply StatMech.Universality.rlc_sequentialExtremalClosedComparison_of_not_mem omega he

/--
[RlcSequentialExtremalExplorationState.pathPairOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma pathPairOpen_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : RlcSequentialExtremalExplorationState gamma gamma'} :
-- imply
  S.rawConfig ∈ rlc_pathPairOpen (gamma, gamma') := by
-- proof
  apply StatMech.Universality.RlcSequentialExtremalExplorationState.pathPairOpen S

/--
[RlcSequentialExtremalExplorationState.rightTrace_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma rightTrace_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : RlcSequentialExtremalExplorationState gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_pathEdges gamma.1) :
-- imply
  S.rawConfig e = true := by
-- proof
  apply StatMech.Universality.RlcSequentialExtremalExplorationState.rightTrace_open S he

/--
[RlcSequentialExtremalExplorationState.leftTrace_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma leftTrace_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : RlcSequentialExtremalExplorationState gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_pathEdges gamma'.1) :
-- imply
  S.rawConfig e = true := by
-- proof
  apply StatMech.Universality.RlcSequentialExtremalExplorationState.leftTrace_open S he

/--
[RlcStoppedExtremalAxisGapProvenance.toExtremalPairCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma toExtremalPairCandidate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {S : RlcStoppedExtremalAxisGapProvenance G hn hlt} :
-- imply
  (rlc_extremalPairCandidate (gamma, gamma')).Nonempty := by
-- proof
  apply StatMech.Universality.RlcStoppedExtremalAxisGapProvenance.toExtremalPairCandidate S

/--
[RlcStoppedExtremalAxisGapProvenance.toFailureSelectedSideTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma toFailureSelectedSideTopology_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {S : RlcStoppedExtremalAxisGapProvenance G hn hlt} :
-- imply
  RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt := by
-- proof
  apply StatMech.Universality.RlcStoppedExtremalAxisGapProvenance.toFailureSelectedSideTopology S

/--
[RlcStoppedExtremalAxisGapProvenance.boundaryArc_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma boundaryArc_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {S : RlcStoppedExtremalAxisGapProvenance G hn hlt}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
-- proof
  apply StatMech.Universality.RlcStoppedExtremalAxisGapProvenance.boundaryArc_of_failure S tau hno

/--
[RlcStoppedExtremalAxisGapProvenance.pims_success_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma pims_success_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {hn : 0 < n}
  {hlt : G.lower + 1 < G.upper}
  {S : RlcStoppedExtremalAxisGapProvenance G hn hlt}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  rlc_axisGapPIMSReflectedConfig G tau ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.RlcStoppedExtremalAxisGapProvenance.pims_success_of_failure S tau hno

/--
[rlc_stoppedPIMSProvenance_of_extremalConstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean)
-/
@[path]
private lemma rlc_stoppedPIMSProvenance_of_extremalConstruction_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hconstruction : RlcExtremalStrataCarryStoppedPIMSProvenance n)
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hselected : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
-- imply
  Nonempty (RlcStoppedExtremalAxisGapProvenance G hn hlt) := by
-- proof
  apply StatMech.Universality.rlc_stoppedPIMSProvenance_of_extremalConstruction hconstruction G hn hlt hselected


-- created on 2026-10-23
