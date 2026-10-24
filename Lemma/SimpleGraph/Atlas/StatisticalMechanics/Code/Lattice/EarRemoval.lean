import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.EarRemoval
open SimpleGraph Function StatMech StatMech.Lattice


/--
[orbitStep_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma orbitStep_partition_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  rightCornerCount K e p + straightStepCount K e p + leftCornerCount K e p = (p : ℤ) := by
-- proof
  apply StatMech.Lattice.orbitStep_partition K e p

/--
[totalTurnZ_eq_rl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma totalTurnZ_eq_rl_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
  {r l : ℤ}
-- given
  (hr : rightCornerCount K e p = r)
  (hl : leftCornerCount K e p = l) :
-- imply
  totalTurnZ K e p = r - l := by
-- proof
  apply StatMech.Lattice.totalTurnZ_eq_rl K e p hr hl

/--
[totalTurnZ_neg_four_of_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma totalTurnZ_neg_four_of_convex_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (hr : rightCornerCount K e p = 0)
  (hl : leftCornerCount K e p = 4) :
-- imply
  totalTurnZ K e p = -4 := by
-- proof
  apply StatMech.Lattice.totalTurnZ_neg_four_of_convex K e p hr hl

/--
[totalTurnZ_four_of_reflexFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma totalTurnZ_four_of_reflexFree_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (hr : rightCornerCount K e p = 4)
  (hl : leftCornerCount K e p = 0) :
-- imply
  totalTurnZ K e p = 4 := by
-- proof
  apply StatMech.Lattice.totalTurnZ_four_of_reflexFree K e p hr hl

/--
[turningIsFullRevolution_of_corner_diff_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_corner_diff_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : rightCornerCount K a.1 (dartOrbitPeriod K a) - leftCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨ rightCornerCount K a.1 (dartOrbitPeriod K a) - leftCornerCount K a.1 (dartOrbitPeriod K a) = -4) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_corner_diff_four K a h

/--
[turningIsFullRevolution_of_canonical_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_canonical_convex_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hr : rightCornerCount K a.1 (dartOrbitPeriod K a) = 0)
  (hl : leftCornerCount K a.1 (dartOrbitPeriod K a) = 4) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_canonical_convex K a hr hl

/--
[turningIsFullRevolution_of_canonical_reflexFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_canonical_reflexFree_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hr : rightCornerCount K a.1 (dartOrbitPeriod K a) = 4)
  (hl : leftCornerCount K a.1 (dartOrbitPeriod K a) = 0) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_canonical_reflexFree K a hr hl

/--
[earTurnReplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma earTurnReplacement_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {p p' : ℕ}
  {r l r' l' : ℤ}
-- given
  (hr : rightCornerCount K e p = r)
  (hl : leftCornerCount K e p = l)
  (hr' : rightCornerCount K' e' p' = r')
  (hl' : leftCornerCount K' e' p' = l')
  (hbal : r - l = r' - l') :
-- imply
  totalTurnZ K e p = totalTurnZ K' e' p' := by
-- proof
  apply StatMech.Lattice.earTurnReplacement K K' e e' p p' hr hl hr' hl' hbal

/--
[turningIsFullRevolution_of_balance_eq_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_balance_eq_base_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hbase : rightCornerCount K a.1 (dartOrbitPeriod K a) - leftCornerCount K a.1 (dartOrbitPeriod K a) = rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) - leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_balance_eq_base K a hbase

/--
[turningIsFullRevolution_of_simplePolygon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_simplePolygon_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : SimplePolygonCornerBalance K a) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_simplePolygon K a h

/--
[simplePolygonCornerBalance_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma simplePolygonCornerBalance_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  SimplePolygonCornerBalance K a ↔ TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.simplePolygonCornerBalance_iff K a

/--
[unitCell_simplePolygonCornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma unitCell_simplePolygonCornerBalance_eq :
-- imply
  SimplePolygonCornerBalance unitCell ucBase := by
-- proof
  apply StatMech.Lattice.unitCell_simplePolygonCornerBalance

/--
[domino_eq_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma domino_eq_insert_eq :
-- imply
  domino = insert (![0, 0] : Site 2) {![1, 0]} := by
-- proof
  apply StatMech.Lattice.domino_eq_insert

/--
[domino_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma domino_finite_eq :
-- imply
  domino.Finite := by
-- proof
  apply StatMech.Lattice.domino_finite

/--
[mem_domino_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma mem_domino_iff_eq
  {v : Site 2} :
-- imply
  v ∈ domino ↔ v = ![0, 0] ∨ v = ![1, 0] := by
-- proof
  apply StatMech.Lattice.mem_domino_iff v

/--
[origin_mem_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma origin_mem_domino_eq :
-- imply
  (![0, 0] : Site 2) ∈ domino := by
-- proof
  apply StatMech.Lattice.origin_mem_domino

/--
[one_mem_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma one_mem_domino_eq :
-- imply
  (![1, 0] : Site 2) ∈ domino := by
-- proof
  apply StatMech.Lattice.one_mem_domino

/--
[mem_domino_coord_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma mem_domino_coord_iff_eq
  {v : Site 2} :
-- imply
  v ∈ domino ↔ (v 0 = 0 ∧ v 1 = 0) ∨ (v 0 = 1 ∧ v 1 = 0) := by
-- proof
  apply StatMech.Lattice.mem_domino_coord_iff v

/--
[not_mem_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma not_mem_domino_eq
  {v : Site 2}
-- given
  (h : ¬ ((v 0 = 0 ∧ v 1 = 0) ∨ (v 0 = 1 ∧ v 1 = 0))) :
-- imply
  v ∉ domino := by
-- proof
  apply StatMech.Lattice.not_mem_domino v h

/--
[dmD0_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD0_tail_eq :
-- imply
  dmD0.tail = ![0, 0] := by
-- proof
  apply StatMech.Lattice.dmD0_tail

/--
[dmD1_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD1_tail_eq :
-- imply
  dmD1.tail = ![0, 0] := by
-- proof
  apply StatMech.Lattice.dmD1_tail

/--
[dmD2_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD2_tail_eq :
-- imply
  dmD2.tail = ![0, 0] := by
-- proof
  apply StatMech.Lattice.dmD2_tail

/--
[dmD3_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD3_tail_eq :
-- imply
  dmD3.tail = ![1, 0] := by
-- proof
  apply StatMech.Lattice.dmD3_tail

/--
[dmD4_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD4_tail_eq :
-- imply
  dmD4.tail = ![1, 0] := by
-- proof
  apply StatMech.Lattice.dmD4_tail

/--
[dmD5_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD5_tail_eq :
-- imply
  dmD5.tail = ![1, 0] := by
-- proof
  apply StatMech.Lattice.dmD5_tail

/--
[dmD0_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD0_dir_eq :
-- imply
  dmD0.dir = ![0, -1] := by
-- proof
  apply StatMech.Lattice.dmD0_dir

/--
[dmD1_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD1_dir_eq :
-- imply
  dmD1.dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.dmD1_dir

/--
[dmD2_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD2_dir_eq :
-- imply
  dmD2.dir = ![0, 1] := by
-- proof
  apply StatMech.Lattice.dmD2_dir

/--
[dmD3_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD3_dir_eq :
-- imply
  dmD3.dir = ![0, 1] := by
-- proof
  apply StatMech.Lattice.dmD3_dir

/--
[dmD4_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD4_dir_eq :
-- imply
  dmD4.dir = ![1, 0] := by
-- proof
  apply StatMech.Lattice.dmD4_dir

/--
[dmD5_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD5_dir_eq :
-- imply
  dmD5.dir = ![0, -1] := by
-- proof
  apply StatMech.Lattice.dmD5_dir

/--
[dmD0_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD0_head_eq :
-- imply
  dmD0.head = ![0, -1] := by
-- proof
  apply StatMech.Lattice.dmD0_head

/--
[dmD1_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD1_head_eq :
-- imply
  dmD1.head = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.dmD1_head

/--
[dmD2_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD2_head_eq :
-- imply
  dmD2.head = ![0, 1] := by
-- proof
  apply StatMech.Lattice.dmD2_head

/--
[dmD3_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD3_head_eq :
-- imply
  dmD3.head = ![1, 1] := by
-- proof
  apply StatMech.Lattice.dmD3_head

/--
[dmD4_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD4_head_eq :
-- imply
  dmD4.head = ![2, 0] := by
-- proof
  apply StatMech.Lattice.dmD4_head

/--
[dmD5_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD5_head_eq :
-- imply
  dmD5.head = ![1, -1] := by
-- proof
  apply StatMech.Lattice.dmD5_head

/--
[dmD0_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD0_boundary_eq :
-- imply
  IsBoundaryDart domino dmD0 := by
-- proof
  apply StatMech.Lattice.dmD0_boundary

/--
[dmD0_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD0_travel_eq :
-- imply
  -rot90Fun dmD0.dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.dmD0_travel

/--
[dmD1_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD1_travel_eq :
-- imply
  -rot90Fun dmD1.dir = ![0, 1] := by
-- proof
  apply StatMech.Lattice.dmD1_travel

/--
[dmD2_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD2_travel_eq :
-- imply
  -rot90Fun dmD2.dir = ![1, 0] := by
-- proof
  apply StatMech.Lattice.dmD2_travel

/--
[dmD3_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD3_travel_eq :
-- imply
  -rot90Fun dmD3.dir = ![1, 0] := by
-- proof
  apply StatMech.Lattice.dmD3_travel

/--
[dmD4_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD4_travel_eq :
-- imply
  -rot90Fun dmD4.dir = ![0, -1] := by
-- proof
  apply StatMech.Lattice.dmD4_travel

/--
[dmD5_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD5_travel_eq :
-- imply
  -rot90Fun dmD5.dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.dmD5_travel

/--
[dmD0_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD0_front_nmem_eq :
-- imply
  dmD0.head + (-rot90Fun dmD0.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD0_front_nmem

/--
[dmD0_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD0_side_nmem_eq :
-- imply
  dmD0.tail + (-rot90Fun dmD0.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD0_side_nmem

/--
[dmD1_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD1_front_nmem_eq :
-- imply
  dmD1.head + (-rot90Fun dmD1.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD1_front_nmem

/--
[dmD1_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD1_side_nmem_eq :
-- imply
  dmD1.tail + (-rot90Fun dmD1.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD1_side_nmem

/--
[dmD2_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD2_front_nmem_eq :
-- imply
  dmD2.head + (-rot90Fun dmD2.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD2_front_nmem

/--
[dmD2_side_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD2_side_mem_eq :
-- imply
  dmD2.tail + (-rot90Fun dmD2.dir) ∈ domino := by
-- proof
  apply StatMech.Lattice.dmD2_side_mem

/--
[dmD3_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD3_front_nmem_eq :
-- imply
  dmD3.head + (-rot90Fun dmD3.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD3_front_nmem

/--
[dmD3_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD3_side_nmem_eq :
-- imply
  dmD3.tail + (-rot90Fun dmD3.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD3_side_nmem

/--
[dmD4_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD4_front_nmem_eq :
-- imply
  dmD4.head + (-rot90Fun dmD4.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD4_front_nmem

/--
[dmD4_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD4_side_nmem_eq :
-- imply
  dmD4.tail + (-rot90Fun dmD4.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD4_side_nmem

/--
[dmD5_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD5_front_nmem_eq :
-- imply
  dmD5.head + (-rot90Fun dmD5.dir) ∉ domino := by
-- proof
  apply StatMech.Lattice.dmD5_front_nmem

/--
[dmD5_side_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD5_side_mem_eq :
-- imply
  dmD5.tail + (-rot90Fun dmD5.dir) ∈ domino := by
-- proof
  apply StatMech.Lattice.dmD5_side_mem

/--
[dmD0_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD0_turnZ_eq :
-- imply
  turnZ domino dmD0 = -1 := by
-- proof
  apply StatMech.Lattice.dmD0_turnZ

/--
[dmD1_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD1_turnZ_eq :
-- imply
  turnZ domino dmD1 = -1 := by
-- proof
  apply StatMech.Lattice.dmD1_turnZ

/--
[dmD2_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD2_turnZ_eq :
-- imply
  turnZ domino dmD2 = 0 := by
-- proof
  apply StatMech.Lattice.dmD2_turnZ

/--
[dmD3_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD3_turnZ_eq :
-- imply
  turnZ domino dmD3 = -1 := by
-- proof
  apply StatMech.Lattice.dmD3_turnZ

/--
[dmD4_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD4_turnZ_eq :
-- imply
  turnZ domino dmD4 = -1 := by
-- proof
  apply StatMech.Lattice.dmD4_turnZ

/--
[dmD5_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmD5_turnZ_eq :
-- imply
  turnZ domino dmD5 = 0 := by
-- proof
  apply StatMech.Lattice.dmD5_turnZ

/--
[dartNext_dmD0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dartNext_dmD0_eq :
-- imply
  dartNext domino dmD0 = dmD1 := by
-- proof
  apply StatMech.Lattice.dartNext_dmD0

/--
[dartNext_dmD1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dartNext_dmD1_eq :
-- imply
  dartNext domino dmD1 = dmD2 := by
-- proof
  apply StatMech.Lattice.dartNext_dmD1

/--
[dartNext_dmD2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dartNext_dmD2_eq :
-- imply
  dartNext domino dmD2 = dmD3 := by
-- proof
  apply StatMech.Lattice.dartNext_dmD2

/--
[dartNext_dmD3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dartNext_dmD3_eq :
-- imply
  dartNext domino dmD3 = dmD4 := by
-- proof
  apply StatMech.Lattice.dartNext_dmD3

/--
[dartNext_dmD4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dartNext_dmD4_eq :
-- imply
  dartNext domino dmD4 = dmD5 := by
-- proof
  apply StatMech.Lattice.dartNext_dmD4

/--
[dartNext_dmD5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dartNext_dmD5_eq :
-- imply
  dartNext domino dmD5 = dmD0 := by
-- proof
  apply StatMech.Lattice.dartNext_dmD5

/--
[iterate_dmD_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma iterate_dmD_1_eq :
-- imply
  (dartNext domino)^[1] dmD0 = dmD1 := by
-- proof
  apply StatMech.Lattice.iterate_dmD_1

/--
[iterate_dmD_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma iterate_dmD_2_eq :
-- imply
  (dartNext domino)^[2] dmD0 = dmD2 := by
-- proof
  apply StatMech.Lattice.iterate_dmD_2

/--
[iterate_dmD_3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma iterate_dmD_3_eq :
-- imply
  (dartNext domino)^[3] dmD0 = dmD3 := by
-- proof
  apply StatMech.Lattice.iterate_dmD_3

/--
[iterate_dmD_4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma iterate_dmD_4_eq :
-- imply
  (dartNext domino)^[4] dmD0 = dmD4 := by
-- proof
  apply StatMech.Lattice.iterate_dmD_4

/--
[iterate_dmD_5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma iterate_dmD_5_eq :
-- imply
  (dartNext domino)^[5] dmD0 = dmD5 := by
-- proof
  apply StatMech.Lattice.iterate_dmD_5

/--
[iterate_dmD_6](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma iterate_dmD_6_eq :
-- imply
  (dartNext domino)^[6] dmD0 = dmD0 := by
-- proof
  apply StatMech.Lattice.iterate_dmD_6

/--
[domino_totalTurnZ_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma domino_totalTurnZ_six_eq :
-- imply
  totalTurnZ domino dmD0 6 = -4 := by
-- proof
  apply StatMech.Lattice.domino_totalTurnZ_six

/--
[dmBase_isPeriodicPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmBase_isPeriodicPt_eq :
-- imply
  Function.IsPeriodicPt (dartNextSub domino) 6 dmBase := by
-- proof
  apply StatMech.Lattice.dmBase_isPeriodicPt

/--
[dmBase_not_periodic_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmBase_not_periodic_two_eq :
-- imply
  ¬ Function.IsPeriodicPt (dartNextSub domino) 2 dmBase := by
-- proof
  apply StatMech.Lattice.dmBase_not_periodic_two

/--
[dmBase_not_periodic_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmBase_not_periodic_three_eq :
-- imply
  ¬ Function.IsPeriodicPt (dartNextSub domino) 3 dmBase := by
-- proof
  apply StatMech.Lattice.dmBase_not_periodic_three

/--
[dmBase_not_fixedPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma dmBase_not_fixedPt_eq :
-- imply
  ¬ Function.IsFixedPt (dartNextSub domino) dmBase := by
-- proof
  apply StatMech.Lattice.dmBase_not_fixedPt

/--
[domino_orbitPeriod_eq_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma domino_orbitPeriod_eq_six_eq :
-- imply
  dartOrbitPeriod domino dmBase = 6 := by
-- proof
  apply StatMech.Lattice.domino_orbitPeriod_eq_six

/--
[domino_turningIsFullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma domino_turningIsFullRevolution_eq :
-- imply
  TurningIsFullRevolution domino dmBase := by
-- proof
  apply StatMech.Lattice.domino_turningIsFullRevolution

/--
[domino_simplePolygonCornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean)
-/
@[path]
private lemma domino_simplePolygonCornerBalance_eq :
-- imply
  SimplePolygonCornerBalance domino dmBase := by
-- proof
  apply StatMech.Lattice.domino_simplePolygonCornerBalance


-- created on 2026-10-23
