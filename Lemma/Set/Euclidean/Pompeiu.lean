import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.Pompeiu
open MetaMathlibExt


/--
[pompeiu_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Pompeiu.lean)
-/
@[path]
private lemma pompeiu_general_eq
  {A B C P : EuclideanSpace ℝ (Fin 2)}
-- given
  (h_equilateral : dist A B = dist B C ∧ dist B C = dist C A)
  (h_side_pos : 0 < dist A B) :
-- imply
  dist P A ≤ dist P B + dist P C ∧
      dist P B ≤ dist P C + dist P A ∧
      dist P C ≤ dist P A + dist P B := by
-- proof
  apply MetaMathlibExt.pompeiu_general A B C P h_equilateral h_side_pos

/--
[pompeiu](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Pompeiu.lean)
-/
@[path]
private lemma pompeiu_eq
  {A B C P : EuclideanSpace ℝ (Fin 2)}
-- given
  (h_equilateral : dist A B = dist B C ∧ dist B C = dist C A)
  (h_side_pos : 0 < dist A B)
  (hP : P ≠ A ∧ P ≠ B ∧ P ≠ C) :
-- imply
  dist P A ≤ dist P B + dist P C ∧
      dist P B ≤ dist P C + dist P A ∧
      dist P C ≤ dist P A + dist P B := by
-- proof
  apply MetaMathlibExt.pompeiu A B C P h_equilateral h_side_pos hP


-- created on 2026-10-20
