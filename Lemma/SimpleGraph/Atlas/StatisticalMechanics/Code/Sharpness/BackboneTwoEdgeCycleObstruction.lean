import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part9
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneTwoEdgeCycleObstruction


/--
[graph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma graph_edgeFinset_eq :
-- imply
  graph.edgeFinset = {s((0 : Fin 6), 1), s((1 : Fin 6), 2), s((3 : Fin 6), 4), s((4 : Fin 6), 5), s((5 : Fin 6), 3)} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.graph_edgeFinset

/--
[headEdge_ne_suffixEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma headEdge_ne_suffixEdge_eq :
-- imply
  headEdge ≠ suffixEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.headEdge_ne_suffixEdge

/--
[headEdge_ne_cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma headEdge_ne_cycleEdge_eq :
-- imply
  headEdge ≠ cycleEdge₀ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.headEdge_ne_cycleEdge

/--
[headEdge_ne_cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma headEdge_ne_cycleEdge_eq_2 :
-- imply
  headEdge ≠ cycleEdge₁ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.headEdge_ne_cycleEdge

/--
[headEdge_ne_cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma headEdge_ne_cycleEdge_eq_3 :
-- imply
  headEdge ≠ cycleEdge₂ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.headEdge_ne_cycleEdge

/--
[suffixEdge_ne_cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEdge_ne_cycleEdge_eq :
-- imply
  suffixEdge ≠ cycleEdge₀ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEdge_ne_cycleEdge

/--
[suffixEdge_ne_cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEdge_ne_cycleEdge_eq_2 :
-- imply
  suffixEdge ≠ cycleEdge₁ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEdge_ne_cycleEdge

/--
[suffixEdge_ne_cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEdge_ne_cycleEdge_eq_3 :
-- imply
  suffixEdge ≠ cycleEdge₂ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEdge_ne_cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq :
-- imply
  cycleEdge₀ ≠ cycleEdge₁ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_2 :
-- imply
  cycleEdge₀ ≠ cycleEdge₂ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_3 :
-- imply
  cycleEdge₁ ≠ cycleEdge₂ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[suffixEdge_ne_headEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEdge_ne_headEdge_eq :
-- imply
  suffixEdge ≠ headEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEdge_ne_headEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_4 :
-- imply
  cycleEdge₀ ≠ headEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_5 :
-- imply
  cycleEdge₁ ≠ headEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_6 :
-- imply
  cycleEdge₂ ≠ headEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_7 :
-- imply
  cycleEdge₀ ≠ suffixEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_8 :
-- imply
  cycleEdge₁ ≠ suffixEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_9 :
-- imply
  cycleEdge₂ ≠ suffixEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_10 :
-- imply
  cycleEdge₁ ≠ cycleEdge₀ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_11 :
-- imply
  cycleEdge₂ ≠ cycleEdge₀ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[cycleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma cycleEdge_eq_12 :
-- imply
  cycleEdge₂ ≠ cycleEdge₁ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.cycleEdge

/--
[domain_graph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma domain_graph_eq :
-- imply
  domain.graph = graph := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.domain_graph

/--
[head_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma head_active_eq :
-- imply
  canonicalEdgeSegment graph headEdge ∈ domain.active := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.head_active

/--
[suffix_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffix_active_eq :
-- imply
  canonicalEdgeSegment graph suffixEdge ∈ domain.active := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffix_active

/--
[edge_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma edge_cases_eq
  {e : domain.graph.edgeFinset} :
-- imply
  e = headEdge ∨ e = suffixEdge ∨ e = cycleEdge₀ ∨ e = cycleEdge₁ ∨ e = cycleEdge₂ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.edge_cases e

/--
[superposition_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma superposition_head_eq :
-- imply
  superposition headEdge = 1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.superposition_head

/--
[superposition_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma superposition_suffix_eq :
-- imply
  superposition suffixEdge = 1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.superposition_suffix

/--
[superposition_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma superposition_cycle_eq :
-- imply
  superposition cycleEdge₀ = 2 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.superposition_cycle

/--
[superposition_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma superposition_cycle_eq_2 :
-- imply
  superposition cycleEdge₁ = 2 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.superposition_cycle

/--
[superposition_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma superposition_cycle_eq_3 :
-- imply
  superposition cycleEdge₂ = 2 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.superposition_cycle

/--
[oddCycleFlux_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycleFlux_head_eq :
-- imply
  oddCycleFlux headEdge = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycleFlux_head

/--
[oddCycleFlux_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycleFlux_suffix_eq :
-- imply
  oddCycleFlux suffixEdge = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycleFlux_suffix

/--
[oddCycleFlux_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycleFlux_cycle_eq :
-- imply
  oddCycleFlux cycleEdge₀ = 1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycleFlux_cycle

/--
[oddCycleFlux_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycleFlux_cycle_eq_2 :
-- imply
  oddCycleFlux cycleEdge₁ = 1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycleFlux_cycle

/--
[oddCycleFlux_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycleFlux_cycle_eq_3 :
-- imply
  oddCycleFlux cycleEdge₂ = 1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycleFlux_cycle

/--
[unitHead_le_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma unitHead_le_superposition_eq :
-- imply
  unitFlux domain.graph headEdge ≤ superposition := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.unitHead_le_superposition

/--
[oddCycleFlux_le_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycleFlux_le_superposition_eq :
-- imply
  oddCycleFlux ≤ superposition := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycleFlux_le_superposition

/--
[profileFlux_headSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma profileFlux_headSplit_eq :
-- imply
  profileFlux domain.graph superposition headSplit = unitFlux domain.graph headEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.profileFlux_headSplit

/--
[profileFlux_oddCycleSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma profileFlux_oddCycleSplit_eq :
-- imply
  profileFlux domain.graph superposition oddCycleSplit = oddCycleFlux := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.profileFlux_oddCycleSplit

/--
[suffixEvenFlux_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEvenFlux_head_eq :
-- imply
  suffixEvenFlux headEdge = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEvenFlux_head

/--
[suffixEvenFlux_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEvenFlux_suffix_eq :
-- imply
  suffixEvenFlux suffixEdge = 1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEvenFlux_suffix

/--
[suffixEvenFlux_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEvenFlux_cycle_eq :
-- imply
  suffixEvenFlux cycleEdge₀ = 2 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEvenFlux_cycle

/--
[suffixEvenFlux_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEvenFlux_cycle_eq_2 :
-- imply
  suffixEvenFlux cycleEdge₁ = 2 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEvenFlux_cycle

/--
[suffixEvenFlux_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEvenFlux_cycle_eq_3 :
-- imply
  suffixEvenFlux cycleEdge₂ = 2 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEvenFlux_cycle

/--
[unitHead_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma unitHead_head_eq :
-- imply
  unitFlux domain.graph headEdge headEdge = 1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.unitHead_head

/--
[unitHead_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma unitHead_suffix_eq :
-- imply
  unitFlux domain.graph headEdge suffixEdge = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.unitHead_suffix

/--
[unitHead_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma unitHead_cycle_eq :
-- imply
  unitFlux domain.graph headEdge cycleEdge₀ = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.unitHead_cycle

/--
[unitHead_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma unitHead_cycle_eq_2 :
-- imply
  unitFlux domain.graph headEdge cycleEdge₁ = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.unitHead_cycle

/--
[unitHead_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma unitHead_cycle_eq_3 :
-- imply
  unitFlux domain.graph headEdge cycleEdge₂ = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.unitHead_cycle

/--
[superposition_sub_unitHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma superposition_sub_unitHead_eq :
-- imply
  (fun e => superposition e - unitFlux domain.graph headEdge e) = suffixEvenFlux := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.superposition_sub_unitHead

/--
[profileFlux_headSplit_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma profileFlux_headSplit_compl_eq :
-- imply
  profileFlux domain.graph superposition (univ \ headSplit) = suffixEvenFlux := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.profileFlux_headSplit_compl

/--
[extendFlux_restrictResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma extendFlux_restrictResidual_eq
  {p : domain.graph.edgeFinset → Nat}
-- given
  (hp : p headEdge = 0) :
-- imply
  extendFlux residualLe (restrictResidual p) = p := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.extendFlux_restrictResidual p hp

/--
[residualCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma residualCycle_eq :
-- imply
  residualCycle₀ ≠ residualSuffix := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.residualCycle

/--
[residual_complete_suffixEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma residual_complete_suffixEven_eq :
-- imply
  BackboneTwoEdgeBondProgram.program.CompleteEvent (shb_BackboneExplorationDomain.advance domain (canonicalEdgeSegment domain.graph headEdge)) [canonicalEdgeSegment domain.graph suffixEdge] (restrictResidual suffixEvenFlux) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.residual_complete_suffixEven

/--
[suffixEven_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffixEven_event_eq :
-- imply
  ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph suffixEvenFlux := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffixEven_event

/--
[sources_unitFlux_eq_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma sources_unitFlux_eq_toFinset_eq
  {e : domain.graph.edgeFinset} :
-- imply
  sources domain.graph (ofEdgeFun domain.graph (unitFlux domain.graph e)) = e.1.toFinset := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.sources_unitFlux_eq_toFinset e

/--
[oddCycle_sources_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycle_sources_empty_eq :
-- imply
  sources domain.graph (ofEdgeFun domain.graph oddCycleFlux) = ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycle_sources_empty

/--
[oddCycle_vacuum_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycle_vacuum_event_eq :
-- imply
  (residualVacuumRunSpec domain (canonicalEdgeSegment domain.graph headEdge)).Event domain.graph oddCycleFlux := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycle_vacuum_event

/--
[suffix_event_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma suffix_event_cycle_eq
  {p : domain.graph.edgeFinset → Nat}
-- given
  (h : ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph p) :
-- imply
  ¬ Odd (p cycleEdge₀) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.suffix_event_cycle p h

/--
[oddCycleSplit_filter_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma oddCycleSplit_filter_cycle_eq :
-- imply
  oddCycleSplit.filter (fun i : Copy domain.graph superposition => i.1 = cycleEdge₀) = {cycle₀Copy₀} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.oddCycleSplit_filter_cycle

/--
[filter_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma filter_symmDiff_eq
  {S T : Finset (Copy domain.graph superposition)} :
-- imply
  (S ∆ T).filter (fun i => i.1 = cycleEdge₀) = S.filter (fun i => i.1 = cycleEdge₀) ∆ T.filter (fun i => i.1 = cycleEdge₀) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.filter_symmDiff S T

/--
[odd_card_symmDiff_singleton_iff_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma odd_card_symmDiff_singleton_iff_not_eq
  [DecidableEq A]
  {S : Finset A}
  {a : A} :
-- imply
  Odd #(S ∆ {a}) ↔ ¬ Odd #S := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.odd_card_symmDiff_singleton_iff_not S a

/--
[profile_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma profile_cycle_eq
  {T : Finset (Copy domain.graph superposition)} :
-- imply
  Odd (profileFlux domain.graph superposition (T ∆ oddCycleSplit) cycleEdge₀) ↔ ¬ Odd (profileFlux domain.graph superposition T cycleEdge₀) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.profile_cycle T

/--
[profileFlux_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma profileFlux_empty_eq :
-- imply
  profileFlux domain.graph superposition (∅ : Finset (Copy domain.graph superposition)) = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.profileFlux_empty

/--
[no_residualVacuum_suffix_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma no_residualVacuum_suffix_covariance_eq
  {path : Finset (Copy domain.graph superposition)} :
-- imply
  ¬ BondwiseRunToggleCovariance (residualVacuumRunSpec domain (canonicalEdgeSegment domain.graph headEdge)) ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]) domain.graph superposition path := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.no_residualVacuum_suffix_covariance path

/--
[superposition_weight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma superposition_weight_pos_eq
  {beta : Real}
  {J : Sym2 (Fin 6) → Real}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g) :
-- imply
  0 < weight domain.graph beta J (ofEdgeFun domain.graph superposition) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.superposition_weight_pos beta J hbeta hJ

/--
[right_rawPairFiberMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma right_rawPairFiberMass_pos_eq
  {beta : Real}
  {J : Sym2 (Fin 6) → Real}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g) :
-- imply
  0 < rawSourcePairFiberMass domain.graph beta J superposition (((BackboneTwoEdgeBondProgram.selectorSpec (V := Fin 6)).toPartialSelector.sourceClass domain [canonicalEdgeSegment domain.graph headEdge, canonicalEdgeSegment domain.graph suffixEdge]) ∆ stepToggleSource (BackboneTwoEdgeBondProgram.selectorSpec (V := Fin 6)).toPartialSelector domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]) (shb_ActiveSegmentFiber domain (canonicalEdgeSegment domain.graph headEdge) head_active) (liftedResidualFiber (BackboneTwoEdgeBondProgram.selectorSpec (V := Fin 6)).toPartialSelector domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.right_rawPairFiberMass_pos beta J hbeta hJ

/--
[coordinatePairContributes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma coordinatePairContributes_eq
  {beta : Real}
  {J : Sym2 (Fin 6) → Real}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g) :
-- imply
  CoordinatePairContributes (BackboneTwoEdgeBondProgram.selectorSpec (V := Fin 6)).toPartialSelector beta J domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge] head_active superposition := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.coordinatePairContributes beta J hbeta hJ

/--
[not_canonicalComponentwiseToggleExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean)
-/
@[path]
private lemma not_canonicalComponentwiseToggleExists_eq
  {beta : Real}
  {J : Sym2 (Fin 6) → Real}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g) :
-- imply
  ¬ (BackboneTwoEdgeBondProgram.selectorSpec (V := Fin 6)).CanonicalComponentwiseToggleExists beta J domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge] head_active := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCycleObstruction.not_canonicalComponentwiseToggleExists beta J hbeta hJ


-- created on 2026-10-23
