import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBoundaryAlignedLocalObstruction
open StatMech StatMech.FrontierD


/--
[boundaryAlignedObstructionP_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean)
-/
@[path]
private lemma boundaryAlignedObstructionP_ice_eq :
-- imply
  boundaryAlignedObstructionP.Ice := by
-- proof
  apply StatMech.FrontierD.boundaryAlignedObstructionP_ice

/--
[boundaryAlignedObstructionQ_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean)
-/
@[path]
private lemma boundaryAlignedObstructionQ_ice_eq :
-- imply
  boundaryAlignedObstructionQ.Ice := by
-- proof
  apply StatMech.FrontierD.boundaryAlignedObstructionQ_ice

/--
[boundaryAlignedObstruction_degree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean)
-/
@[path]
private lemma boundaryAlignedObstruction_degree_two_eq :
-- imply
  (sixVertexLocalDisagreementSides boundaryAlignedObstructionP boundaryAlignedObstructionQ).card = 2 := by
-- proof
  apply StatMech.FrontierD.boundaryAlignedObstruction_degree_two

/--
[boundaryAlignedObstruction_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean)
-/
@[path]
private lemma boundaryAlignedObstruction_compatible_eq :
-- imply
  compatible false boundaryAlignedObstructionP /\ compatible true boundaryAlignedObstructionQ := by
-- proof
  apply StatMech.FrontierD.boundaryAlignedObstruction_compatible

/--
[boundaryAlignedObstruction_target_patterns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean)
-/
@[path]
private lemma boundaryAlignedObstruction_target_patterns_eq
  {targetPairingP targetPairingQ : Bool} :
-- imply
  boundaryAlignedTransportedLocalPattern boundaryAlignedObstructionP boundaryAlignedObstructionQ false true false 2 false true targetPairingP targetPairingQ false = ![true, true, false, false] /\ boundaryAlignedTransportedLocalPattern boundaryAlignedObstructionP boundaryAlignedObstructionQ false true false 2 false true targetPairingP targetPairingQ true = ![false, false, true, true] := by
-- proof
  apply StatMech.FrontierD.boundaryAlignedObstruction_target_patterns targetPairingP targetPairingQ

/--
[boundaryAlignedObstruction_target_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean)
-/
@[path]
private lemma boundaryAlignedObstruction_target_ice_eq
  {targetPairingP targetPairingQ layer : Bool} :
-- imply
  (boundaryAlignedTransportedLocalPattern boundaryAlignedObstructionP boundaryAlignedObstructionQ false true false 2 false true targetPairingP targetPairingQ layer).Ice := by
-- proof
  apply StatMech.FrontierD.boundaryAlignedObstruction_target_ice targetPairingP targetPairingQ layer

/--
[boundaryAlignedTransport_no_exact_localC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean)
-/
@[path]
private lemma boundaryAlignedTransport_no_exact_localC_eq
  {targetPairingP targetPairingQ : Bool} :
-- imply
  localCIndicator (boundaryAlignedTransportedLocalPattern boundaryAlignedObstructionP boundaryAlignedObstructionQ false true false 2 false true targetPairingP targetPairingQ false) + localCIndicator (boundaryAlignedTransportedLocalPattern boundaryAlignedObstructionP boundaryAlignedObstructionQ false true false 2 false true targetPairingP targetPairingQ true) ≠ localCIndicator boundaryAlignedObstructionP + localCIndicator boundaryAlignedObstructionQ := by
-- proof
  apply StatMech.FrontierD.boundaryAlignedTransport_no_exact_localC targetPairingP targetPairingQ


-- created on 2026-10-23
