import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
open SimpleGraph StatMech StatMech.Lattice


/--
[adj_iff_unitWt_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma adj_iff_unitWt_sub_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj x y ↔ unitWt (x - y) = 1 := by
-- proof
  apply StatMech.Lattice.adj_iff_unitWt_sub x y

/--
[unitWt_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma unitWt_neg_eq
  {z : Site 2} :
-- imply
  unitWt (-z) = unitWt z := by
-- proof
  apply StatMech.Lattice.unitWt_neg z

/--
[unitWt_rot90Fun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma unitWt_rot90Fun_eq
  {z : Site 2} :
-- imply
  unitWt (rot90Fun z) = unitWt z := by
-- proof
  apply StatMech.Lattice.unitWt_rot90Fun z

/--
[unitWt_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma unitWt_dir_eq
  {e : Dart} :
-- imply
  unitWt e.dir = 1 := by
-- proof
  apply StatMech.Lattice.unitWt_dir e

/--
[unitWt_rot90Fun_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma unitWt_rot90Fun_dir_eq
  {e : Dart} :
-- imply
  unitWt (rot90Fun e.dir) = 1 := by
-- proof
  apply StatMech.Lattice.unitWt_rot90Fun_dir e

/--
[unitWt_neg_rot90Fun_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma unitWt_neg_rot90Fun_dir_eq
  {e : Dart} :
-- imply
  unitWt (-rot90Fun e.dir) = 1 := by
-- proof
  apply StatMech.Lattice.unitWt_neg_rot90Fun_dir e

/--
[mkDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma mkDart_tail_eq
  {p g : Site 2}
-- given
  (hg : unitWt g = 1) :
-- imply
  (mkDart p g hg).tail = p := by
-- proof
  apply StatMech.Lattice.mkDart_tail p g hg

/--
[mkDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma mkDart_head_eq
  {p g : Site 2}
-- given
  (hg : unitWt g = 1) :
-- imply
  (mkDart p g hg).head = p + g := by
-- proof
  apply StatMech.Lattice.mkDart_head p g hg

/--
[mkDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma mkDart_dir_eq
  {p g : Site 2}
-- given
  (hg : unitWt g = 1) :
-- imply
  (mkDart p g hg).dir = g := by
-- proof
  apply StatMech.Lattice.mkDart_dir p g hg

/--
[IsBoundaryDart.tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma tail_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h : IsBoundaryDart K e) :
-- imply
  e.tail ∈ K := by
-- proof
  apply StatMech.Lattice.IsBoundaryDart.tail_mem h

/--
[IsBoundaryDart.head_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma head_not_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h : IsBoundaryDart K e) :
-- imply
  e.head ∉ K := by
-- proof
  apply StatMech.Lattice.IsBoundaryDart.head_not_mem h

/--
[dartNext_of_front_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma dartNext_of_front_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h : e.head + (-rot90Fun e.dir) ∈ K) :
-- imply
  dartNext K e = mkDart (e.head + (-rot90Fun e.dir)) (rot90Fun e.dir) (unitWt_rot90Fun_dir e) := by
-- proof
  apply StatMech.Lattice.dartNext_of_front_mem K e h

/--
[dartNext_front_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma dartNext_front_head_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h : e.head + (-rot90Fun e.dir) ∈ K) :
-- imply
  (dartNext K e).head = e.head ∧ (dartNext K e).dir = rot90Fun e.dir := by
-- proof
  apply StatMech.Lattice.dartNext_front_head K e h

/--
[dartNext_of_side_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma dartNext_of_side_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∈ K) :
-- imply
  dartNext K e = mkDart (e.tail + (-rot90Fun e.dir)) e.dir (unitWt_dir e) := by
-- proof
  apply StatMech.Lattice.dartNext_of_side_mem K e h0 h1

/--
[dartNext_of_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma dartNext_of_corner_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∉ K) :
-- imply
  dartNext K e = mkDart e.tail (-rot90Fun e.dir) (unitWt_neg_rot90Fun_dir e) := by
-- proof
  apply StatMech.Lattice.dartNext_of_corner K e h0 h1

/--
[dartNext_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean)
-/
@[path]
private lemma dartNext_isBoundaryDart_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  IsBoundaryDart K (dartNext K e) := by
-- proof
  apply StatMech.Lattice.dartNext_isBoundaryDart K e he


-- created on 2026-10-23
