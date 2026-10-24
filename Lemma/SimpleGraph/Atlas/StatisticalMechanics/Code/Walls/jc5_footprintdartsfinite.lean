import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc5_not_avoidsEarFootprint_iff_probes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_not_avoidsEarFootprint_iff_probes_eq
  {r : Site 2}
  {e : Dart} :
-- imply
  ¬ jc3_AvoidsEarFootprint r e ↔ jc5_ProbesEarFootprint r e := by
-- proof
  apply StatMech.Walls.jc5_not_avoidsEarFootprint_iff_probes r e

/--
[jc5_tail_eq_of_tailTravel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_tail_eq_of_tailTravel_eq
  {e : Dart} :
-- imply
  e.tail = jc_tailTravel e + rot90Fun e.dir := by
-- proof
  apply StatMech.Walls.jc5_tail_eq_of_tailTravel e

/--
[jc5_head_eq_of_headTravel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_head_eq_of_headTravel_eq
  {e : Dart} :
-- imply
  e.head = jc_headTravel e + rot90Fun e.dir := by
-- proof
  apply StatMech.Walls.jc5_head_eq_of_headTravel e

/--
[jc5_tailTouching_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_tailTouching_finite_eq
  {r : Site 2} :
-- imply
  {e : Dart | jc_tailTravel e ∈ jc3_earFootprint r}.Finite := by
-- proof
  apply StatMech.Walls.jc5_tailTouching_finite r

/--
[jc5_headTouching_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_headTouching_finite_eq
  {r : Site 2} :
-- imply
  {e : Dart | jc_headTravel e ∈ jc3_earFootprint r}.Finite := by
-- proof
  apply StatMech.Walls.jc5_headTouching_finite r

/--
[jc5_footprintDarts_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_footprintDarts_finite_eq
  {r : Site 2} :
-- imply
  {e : Dart | jc5_ProbesEarFootprint r e}.Finite := by
-- proof
  apply StatMech.Walls.jc5_footprintDarts_finite r

/--
[jc5_touchingDart_tail_dir_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_touchingDart_tail_dir_injOn_eq
  {r : Site 2} :
-- imply
  Set.InjOn (fun e : Dart => (jc_tailTravel e, e.dir)) {e : Dart | jc_tailTravel e ∈ jc3_earFootprint r} := by
-- proof
  apply StatMech.Walls.jc5_touchingDart_tail_dir_injOn r

/--
[jc5_touchingDart_finite_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_touchingDart_finite_image_eq
  {r : Site 2} :
-- imply
  (jc3_earFootprint r ×ˢ {z : Site 2 | unitWt z = 1}).Finite := by
-- proof
  apply StatMech.Walls.jc5_touchingDart_finite_image r

/--
[jc5_farDart_not_probes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_farDart_not_probes_eq :
-- imply
  ¬ jc5_ProbesEarFootprint (![0, 0] : Site 2) jc3_farDart := by
-- proof
  apply StatMech.Walls.jc5_farDart_not_probes

/--
[jc5_someDart_probes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean)
-/
@[path]
private lemma jc5_someDart_probes_eq :
-- imply
  jc5_ProbesEarFootprint (![0, 0] : Site 2) (mkDart (![0, 1] : Site 2) (![1, 0] : Site 2) (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) := by
-- proof
  apply StatMech.Walls.jc5_someDart_probes


-- created on 2026-10-23
