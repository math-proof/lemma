import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[dartFace_tail_of_dir_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dartFace_tail_of_dir_right_eq
  {e : Dart}
-- given
  (hd : e.dir = ![1, 0]) :
-- imply
  e.tail = ![dartFace e 0, dartFace e 1] := by
-- proof
  apply StatMech.Lattice.dartFace_tail_of_dir_right e hd

/--
[dartFace_tail_of_dir_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dartFace_tail_of_dir_left_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1] := by
-- proof
  apply StatMech.Lattice.dartFace_tail_of_dir_left e hd

/--
[dartFace_tail_of_dir_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dartFace_tail_of_dir_up_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  e.tail = ![dartFace e 0 + 1, dartFace e 1] := by
-- proof
  apply StatMech.Lattice.dartFace_tail_of_dir_up e hd

/--
[dartFace_tail_of_dir_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dartFace_tail_of_dir_down_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, -1]) :
-- imply
  e.tail = ![dartFace e 0, dartFace e 1 + 1] := by
-- proof
  apply StatMech.Lattice.dartFace_tail_of_dir_down e hd

/--
[dartFace_eq_of_dir_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dartFace_eq_of_dir_eq_eq
  {e₁ e₂ : Dart}
-- given
  (hdir : e₁.dir = e₂.dir)
  (hface : dartFace e₁ = dartFace e₂) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Lattice.dartFace_eq_of_dir_eq hdir hface

/--
[orbitDart_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma orbitDart_injOn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Set.InjOn (fun k => (dartNext K)^[k] a.1) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Lattice.orbitDart_injOn K a

/--
[orbitFace_injOn_of_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma orbitFace_injOn_of_noPinch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : OrbitFaceNoPinch K a) :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Lattice.orbitFace_injOn_of_noPinch K a h

/--
[orbitFace_noPinch_of_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma orbitFace_noPinch_of_injOn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  OrbitFaceNoPinch K a := by
-- proof
  apply StatMech.Lattice.orbitFace_noPinch_of_injOn K a hinj

/--
[orbitFace_injOn_iff_dir_collision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma orbitFace_injOn_iff_dir_collision_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) ↔ OrbitFaceNoPinch K a := by
-- proof
  apply StatMech.Lattice.orbitFace_injOn_iff_dir_collision K a

/--
[ucFace0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma ucFace0_eq :
-- imply
  dartFace ucDart0 = ![0, 0] := by
-- proof
  apply StatMech.Lattice.ucFace0

/--
[ucFace1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma ucFace1_eq :
-- imply
  dartFace ucDart1 = ![0, -1] := by
-- proof
  apply StatMech.Lattice.ucFace1

/--
[ucFace2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma ucFace2_eq :
-- imply
  dartFace ucDart2 = ![-1, -1] := by
-- proof
  apply StatMech.Lattice.ucFace2

/--
[ucFace3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma ucFace3_eq :
-- imply
  dartFace ucDart3 = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.ucFace3

/--
[unitCell_orbitFace_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma unitCell_orbitFace_injOn_eq :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucDart0)) (Set.Iio 4) := by
-- proof
  apply StatMech.Lattice.unitCell_orbitFace_injOn

/--
[unitCellFaceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma unitCellFaceLoop_isCycle_eq :
-- imply
  unitCellFaceLoop.IsCycle := by
-- proof
  apply StatMech.Lattice.unitCellFaceLoop_isCycle

/--
[dmFace0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dmFace0_eq :
-- imply
  dartFace dmD0 = ![0, -1] := by
-- proof
  apply StatMech.Lattice.dmFace0

/--
[dmFace1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dmFace1_eq :
-- imply
  dartFace dmD1 = ![-1, -1] := by
-- proof
  apply StatMech.Lattice.dmFace1

/--
[dmFace2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dmFace2_eq :
-- imply
  dartFace dmD2 = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.dmFace2

/--
[dmFace3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dmFace3_eq :
-- imply
  dartFace dmD3 = ![0, 0] := by
-- proof
  apply StatMech.Lattice.dmFace3

/--
[dmFace4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dmFace4_eq :
-- imply
  dartFace dmD4 = ![1, 0] := by
-- proof
  apply StatMech.Lattice.dmFace4

/--
[dmFace5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dmFace5_eq :
-- imply
  dartFace dmD5 = ![1, -1] := by
-- proof
  apply StatMech.Lattice.dmFace5

/--
[domino_orbitFace_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma domino_orbitFace_injOn_eq :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext domino)^[k] dmD0)) (Set.Iio 6) := by
-- proof
  apply StatMech.Lattice.domino_orbitFace_injOn

/--
[dominoFaceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean)
-/
@[path]
private lemma dominoFaceLoop_isCycle_eq :
-- imply
  dominoFaceLoop.IsCycle := by
-- proof
  apply StatMech.Lattice.dominoFaceLoop_isCycle


-- created on 2026-10-23
