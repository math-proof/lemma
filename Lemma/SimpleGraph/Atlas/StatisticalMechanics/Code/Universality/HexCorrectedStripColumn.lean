import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
open StatMech StatMech.Universality


/--
[hexCSTopFiniteWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean)
-/
@[path]
private lemma hexCSTopFiniteWeight_nonneg_eq
  {T L : ℕ}
  {ts : List ℤ}
-- given
  (hT : 0 < T) :
-- imply
  0 ≤ hexCSTopFiniteWeight T L hT ts := by
-- proof
  apply StatMech.Universality.hexCSTopFiniteWeight_nonneg T L hT ts

/--
[hexCSTopFiniteWeight_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean)
-/
@[path]
private lemma hexCSTopFiniteWeight_summable_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  Summable (hexCSTopFiniteWeight T L hT) := by
-- proof
  apply StatMech.Universality.hexCSTopFiniteWeight_summable T L hT

/--
[hexCSB_eq_topFiniteWeight_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean)
-/
@[path]
private lemma hexCSB_eq_topFiniteWeight_tsum_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSB T L hT = ∑' ts, hexCSTopFiniteWeight T L hT ts := by
-- proof
  apply StatMech.Universality.hexCSB_eq_topFiniteWeight_tsum T L hT

/--
[hexCSB_le_one_of_exit_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean)
-/
@[path]
private lemma hexCSB_le_one_of_exit_window_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hwindow : HexCSBoundaryWindowLaw T L hT) :
-- imply
  hexCSB T L hT ≤ 1 := by
-- proof
  apply StatMech.Universality.hexCSB_le_one_of_exit_window T L hT hlocal hwindow

/--
[hexCSTopAtWidth_finset_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean)
-/
@[path]
private lemma hexCSTopAtWidth_finset_bound_eq
  {T : ℕ}
  {s : Finset {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}}
-- given
  (hT : 0 < T)
  (hlocal : ∀ L, HexCSLocalRelation T L hT)
  (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  ∑ w ∈ s, hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices ≤ 1 := by
-- proof
  apply StatMech.Universality.hexCSTopAtWidth_finset_bound T hT hlocal hwindow s

/--
[hexCSTopColumn_colSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean)
-/
@[path]
private lemma hexCSTopColumn_colSum_eq
  {T : ℕ}
  {x : ℝ}
-- given
  (hT : 0 < T)
  (hlocal : ∀ L, HexCSLocalRelation T L hT)
  (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  (hexCSTopColumn T hT hlocal hwindow).colSum x = ∑' w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}, x ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices := by
-- proof
  apply StatMech.Universality.hexCSTopColumn_colSum T hT hlocal hwindow x


-- created on 2026-10-23
