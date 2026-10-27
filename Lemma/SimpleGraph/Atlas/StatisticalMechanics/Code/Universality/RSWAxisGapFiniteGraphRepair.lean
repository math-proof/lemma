import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraphRepair
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_scaleTwoDoubleFailure_axisGapEdges_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraphRepair.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_axisGapEdges_ne_empty_eq :
-- imply
  rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap ≠ ∅ := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_axisGapEdges_ne_empty

/--
[rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_has_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraphRepair.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_has_edge_eq :
-- imply
  ∃ x y : RlcConnectorVertex 2, (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).Adj x y := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_has_edge

/--
[rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_ne_connectorFiniteGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraphRepair.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_ne_connectorFiniteGraph_eq :
-- imply
  rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap ≠ rlc_connectorFiniteGraph rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_ne_connectorFiniteGraph


-- created on 2026-10-23
