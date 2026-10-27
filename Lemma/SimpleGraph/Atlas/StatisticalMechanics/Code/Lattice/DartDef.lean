import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
open SimpleGraph StatMech StatMech.Lattice StatMech.Lattice.Dart


/--
[rot90Fun_rot90Fun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma rot90Fun_rot90Fun_eq
  {x : Site 2} :
-- imply
  rot90Fun (rot90Fun x) = -x := by
-- proof
  apply StatMech.Lattice.rot90Fun_rot90Fun x

/--
[rot90Fun_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma rot90Fun_four_eq
  {x : Site 2} :
-- imply
  rot90Fun (rot90Fun (rot90Fun (rot90Fun x))) = x := by
-- proof
  apply StatMech.Lattice.rot90Fun_four x

/--
[rot90Fun_iterate_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma rot90Fun_iterate_four_eq :
-- imply
  rot90Fun ∘ rot90Fun ∘ rot90Fun ∘ rot90Fun = id := by
-- proof
  apply StatMech.Lattice.rot90Fun_iterate_four

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma ext_eq
  {d e : Dart}
-- given
  (ht : d.tail = e.tail)
  (hh : d.head = e.head) :
-- imply
  d = e := by
-- proof
  apply StatMech.Lattice.Dart.ext ht hh

/--
[rev_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma rev_tail_eq
  {d : Dart} :
-- imply
  d.rev.tail = d.head := by
-- proof
  apply StatMech.Lattice.Dart.rev_tail d

/--
[rev_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma rev_head_eq
  {d : Dart} :
-- imply
  d.rev.head = d.tail := by
-- proof
  apply StatMech.Lattice.Dart.rev_head d

/--
[rev_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma rev_rev_eq
  {d : Dart} :
-- imply
  d.rev.rev = d := by
-- proof
  apply StatMech.Lattice.Dart.rev_rev d

/--
[dir_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma dir_def_eq
  {d : Dart} :
-- imply
  d.dir = d.head - d.tail := by
-- proof
  apply StatMech.Lattice.Dart.dir_def d

/--
[dir_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartDef.lean)
-/
@[path]
private lemma dir_rev_eq
  {d : Dart} :
-- imply
  d.rev.dir = - d.dir := by
-- proof
  apply StatMech.Lattice.Dart.dir_rev d


-- created on 2026-10-23
