import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_path_eq_of_edges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_path_eq_of_edges_subset_eq
  {G : SimpleGraph V}
  {u v : V}
  {p q : G.Walk u v}
-- given
  (hp : p.IsPath)
  (hq : q.IsPath)
  (hedges : ∀ e ∈ q.edges, e ∈ p.edges) :
-- imply
  q = p := by
-- proof
  apply StatMech.Universality.rlc_path_eq_of_edges_subset p q hp hq hedges

/--
[rlc_extremalSelectionConfig_right_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelectionConfig_right_edges_eq
  {e : Sym2 (Site 2)}
-- given
  (heOpen : rlc_extremalSelectionCounterexampleConfig e = true)
  (heRect : ∀ x y : Site 2, e = s(x, y) → x ∈ rect 0 2 (-1) 1 ∧ y ∈ rect 0 2 (-1) 1) :
-- imply
  e ∈ rlc_pathEdges rlc_traceSplitCounterexampleRight.1 := by
-- proof
  apply StatMech.Universality.rlc_extremalSelectionConfig_right_edges heOpen heRect

/--
[rlc_extremalSelectionConfig_left_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelectionConfig_left_edges_eq
  {e : Sym2 (Site 2)}
-- given
  (heOpen : rlc_extremalSelectionCounterexampleConfig e = true)
  (heRect : ∀ x y : Site 2, e = s(x, y) → x ∈ rect (-2) 0 (-1) 1 ∧ y ∈ rect (-2) 0 (-1) 1) :
-- imply
  e ∈ rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
-- proof
  apply StatMech.Universality.rlc_extremalSelectionConfig_left_edges heOpen heRect

/--
[rlc_extremalSelection_open_right_edges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_open_right_edges_subset_eq
  {delta : RlcRightDiagonalPath 1}
-- given
  (hopen : rlc_extremalSelectionCounterexampleConfig ∈ rlc_pathOpen delta.1) :
-- imply
  rlc_pathEdges delta.1 ⊆ rlc_pathEdges rlc_traceSplitCounterexampleRight.1 := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_open_right_edges_subset delta hopen

/--
[rlc_extremalSelection_open_left_edges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_open_left_edges_subset_eq
  {delta : RlcLeftDiagonalPath 1}
-- given
  (hopen : rlc_extremalSelectionCounterexampleConfig ∈ rlc_pathOpen delta.1) :
-- imply
  rlc_pathEdges delta.1 ⊆ rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_open_left_edges_subset delta hopen

/--
[rlc_extremalSelection_open_right_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_open_right_start_eq
  {delta : RlcRightDiagonalPath 1}
-- given
  (hopen : rlc_extremalSelectionCounterexampleConfig ∈ rlc_pathOpen delta.1) :
-- imply
  (delta.1.1 : Site 2) = ![0, -1] := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_open_right_start delta hopen

/--
[rlc_extremalSelection_open_right_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_open_right_end_eq
  {delta : RlcRightDiagonalPath 1}
-- given
  (hopen : rlc_extremalSelectionCounterexampleConfig ∈ rlc_pathOpen delta.1) :
-- imply
  (delta.1.2.1 : Site 2) = ![2, 0] := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_open_right_end delta hopen

/--
[rlc_extremalSelection_right_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_right_unique_eq
  {delta : RlcRightDiagonalPath 1}
-- given
  (hopen : rlc_extremalSelectionCounterexampleConfig ∈ rlc_pathOpen delta.1) :
-- imply
  delta = rlc_traceSplitCounterexampleRight := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_right_unique delta hopen

/--
[rlc_extremalSelection_open_left_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_open_left_start_eq
  {delta : RlcLeftDiagonalPath 1}
-- given
  (hopen : rlc_extremalSelectionCounterexampleConfig ∈ rlc_pathOpen delta.1) :
-- imply
  (delta.1.1 : Site 2) = ![-2, 0] := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_open_left_start delta hopen

/--
[rlc_extremalSelection_open_left_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_open_left_end_eq
  {delta : RlcLeftDiagonalPath 1}
-- given
  (hopen : rlc_extremalSelectionCounterexampleConfig ∈ rlc_pathOpen delta.1) :
-- imply
  (delta.1.2.1 : Site 2) = ![0, 1] := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_open_left_end delta hopen

/--
[rlc_extremalSelection_left_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_left_unique_eq
  {delta : RlcLeftDiagonalPath 1}
-- given
  (hopen : rlc_extremalSelectionCounterexampleConfig ∈ rlc_pathOpen delta.1) :
-- imply
  delta = rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_left_unique delta hopen

/--
[rlc_extremalSelection_rightLowestCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_rightLowestCandidate_eq :
-- imply
  rlc_extremalSelectionCounterexampleConfig ∈ rlc_rightLowestCandidate rlc_traceSplitCounterexampleRight := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_rightLowestCandidate

/--
[rlc_extremalSelection_leftHighestCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_leftHighestCandidate_eq :
-- imply
  rlc_extremalSelectionCounterexampleConfig ∈ rlc_leftHighestCandidate rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_leftHighestCandidate

/--
[rlc_extremalSelection_extremalPairCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_extremalPairCandidate_eq :
-- imply
  rlc_extremalSelectionCounterexampleConfig ∈ rlc_extremalPairCandidate (rlc_traceSplitCounterexampleRight, rlc_traceSplitCounterexampleLeft) := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_extremalPairCandidate

/--
[rlc_extremalSelection_and_independent_contact_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean)
-/
@[path]
private lemma rlc_extremalSelection_and_independent_contact_obstruction_eq :
-- imply
  rlc_extremalSelectionCounterexampleConfig ∈ rlc_extremalPairCandidate (rlc_traceSplitCounterexampleRight, rlc_traceSplitCounterexampleLeft) ∧ rlc_windingSideCounterexampleConfig ∉ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧ ¬ RlcLowestHighestReflectedBoundaryContact rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_and_independent_contact_obstruction


-- created on 2026-10-23
