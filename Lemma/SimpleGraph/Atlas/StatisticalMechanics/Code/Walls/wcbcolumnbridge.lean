import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wcbcolumnbridge
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wcb_rayEdge_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_rayEdge_column_eq
  {z x y : Site 2}
-- given
  (h : jec_rayEdge z s(x, y)) :
-- imply
  x 0 = y 0 := by
-- proof
  apply StatMech.Lattice.wcb_rayEdge_column z x y h

/--
[wcb_rayEdge_eq_of_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_rayEdge_eq_of_column_eq
  {z x y : Site 2}
-- given
  (h : jec_rayEdge z s(x, y)) :
-- imply
  s(x, y) = wcb_canonRayEdge z (x 0) := by
-- proof
  apply StatMech.Lattice.wcb_rayEdge_eq_of_column z x y h

/--
[wcb_rayEdge_injOn_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_rayEdge_injOn_column_eq
  {z x₁ y₁ x₂ y₂ : Site 2}
-- given
  (h₁ : jec_rayEdge z s(x₁, y₁))
  (h₂ : jec_rayEdge z s(x₂, y₂))
  (hcol : x₁ 0 = x₂ 0) :
-- imply
  s(x₁, y₁) = s(x₂, y₂) := by
-- proof
  apply StatMech.Lattice.wcb_rayEdge_injOn_column z x₁ y₁ x₂ y₂ h₁ h₂ hcol

/--
[wcb_dartColumn_eq_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_dartColumn_eq_head_eq
  {z : Site 2}
  {d : (hypercubicLattice 2).Dart}
-- given
  (h : jec_rayEdge z s(d.toProd.1, d.toProd.2)) :
-- imply
  wcb_dartColumn d = d.toProd.2 0 := by
-- proof
  apply StatMech.Lattice.wcb_dartColumn_eq_head z d h

/--
[wcb_dart_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_dart_edge_eq
  {d : (hypercubicLattice 2).Dart} :
-- imply
  d.edge = s(d.toProd.1, d.toProd.2) := by
-- proof
  apply StatMech.Lattice.wcb_dart_edge d

/--
[wcb_crossing_edges_distinct_columns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_crossing_edges_distinct_columns_eq
  {z : Site 2}
  {d₁ d₂ : (hypercubicLattice 2).Dart}
-- given
  (h₁ : jec_rayEdge z d₁.edge)
  (h₂ : jec_rayEdge z d₂.edge)
  (hcol : wcb_dartColumn d₁ = wcb_dartColumn d₂) :
-- imply
  d₁.edge = d₂.edge := by
-- proof
  apply StatMech.Lattice.wcb_crossing_edges_distinct_columns z d₁ d₂ h₁ h₂ hcol

/--
[wcb_keyedList_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_keyedList_snd_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  (wcb_keyedList z w).map Prod.snd = wnu_signedList z w := by
-- proof
  apply StatMech.Lattice.wcb_keyedList_snd z w

/--
[wcb_columnOrder_permutes_signedList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_columnOrder_permutes_signedList_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  (wcb_columnSorted z w).Perm (wnu_signedList z w) := by
-- proof
  apply StatMech.Lattice.wcb_columnOrder_permutes_signedList z w

/--
[wcb_columnSorted_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_columnSorted_sum_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  (wcb_columnSorted z w).sum = wnd_signedCross z w := by
-- proof
  apply StatMech.Lattice.wcb_columnSorted_sum z w

/--
[wcb_columnSorted_entries_pm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_columnSorted_entries_pm_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  ∀ s ∈ wcb_columnSorted z w, s = 1 ∨ s = -1 := by
-- proof
  apply StatMech.Lattice.wcb_columnSorted_entries_pm z w

/--
[wcb_columnAlternates_of_sorted_alt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_columnAlternates_of_sorted_alt_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (halt : wnu_Alt (wcb_columnSorted z w)) :
-- imply
  wna_ColumnAlternates z w := by
-- proof
  apply StatMech.Lattice.wcb_columnAlternates_of_sorted_alt z w halt

/--
[wcb_unitSquare_columnSorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_unitSquare_columnSorted_eq :
-- imply
  wcb_columnSorted (![1, 1] : Site 2) wwit_unitSquareLoop = [1] := by
-- proof
  apply StatMech.Lattice.wcb_unitSquare_columnSorted

/--
[wcb_unitSquare_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_unitSquare_columnAlternates_eq :
-- imply
  wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wcb_unitSquare_columnAlternates

/--
[wcb_Ltromino_columnSorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_Ltromino_columnSorted_eq :
-- imply
  wcb_columnSorted (![1, 1] : Site 2) wnu_LtrominoLoop = [-1] := by
-- proof
  apply StatMech.Lattice.wcb_Ltromino_columnSorted

/--
[wcb_Ltromino_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_Ltromino_columnAlternates_eq :
-- imply
  wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wcb_Ltromino_columnAlternates

/--
[wcb_doubleSquare_columnSorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_doubleSquare_columnSorted_eq :
-- imply
  wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare = [1, 1] := by
-- proof
  apply StatMech.Lattice.wcb_doubleSquare_columnSorted

/--
[wcb_doubleSquare_not_columnSorted_alt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean)
-/
@[path]
private lemma wcb_doubleSquare_not_columnSorted_alt_eq :
-- imply
  ¬ wnu_Alt (wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare) := by
-- proof
  apply StatMech.Lattice.wcb_doubleSquare_not_columnSorted_alt


-- created on 2026-10-23
