import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc2_leftfaceextreme
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc2_vertStep_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftfaceextreme.lean)
-/
@[path]
private lemma kc2_vertStep_dir_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
-- proof
  apply StatMech.Walls.kc2_vertStep_dir e hv

/--
[kc2_extremeCell_eq_tail_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftfaceextreme.lean)
-/
@[path]
private lemma kc2_extremeCell_eq_tail_of_left_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) = e.tail := by
-- proof
  apply StatMech.Walls.kc2_extremeCell_eq_tail_of_left e hd

/--
[kc2_extremeCell_mem_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftfaceextreme.lean)
-/
@[path]
private lemma kc2_extremeCell_mem_of_left_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![-1, 0]) :
-- imply
  (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K := by
-- proof
  apply StatMech.Walls.kc2_extremeCell_mem_of_left he hd

/--
[kc2_extremeCell_notMem_of_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftfaceextreme.lean)
-/
@[path]
private lemma kc2_extremeCell_notMem_of_right_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![1, 0]) :
-- imply
  (![dartFace e 0 + 1, dartFace e 1] : Site 2) ∉ K := by
-- proof
  apply StatMech.Walls.kc2_extremeCell_notMem_of_right he hd

/--
[kc2_extremeCell_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftfaceextreme.lean)
-/
@[path]
private lemma kc2_extremeCell_dichotomy_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
-- imply
  (e.dir = ![-1, 0] ∧ (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K) ∨ (e.dir = ![1, 0] ∧ (![dartFace e 0 + 1, dartFace e 1] : Site 2) ∉ K) := by
-- proof
  apply StatMech.Walls.kc2_extremeCell_dichotomy he hv


-- created on 2026-10-23
