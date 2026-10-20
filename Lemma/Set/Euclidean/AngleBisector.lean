import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.AngleBisector
open MetaMathlibExt


/--
[angle_bisector_theorem_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/AngleBisector.lean)
-/
@[path]
private lemma angle_bisector_theorem_general_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
  {A B C D : P}
-- given
  (h_tri : AffineIndependent ℝ (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C))
  (h_bet : Sbtw ℝ B D C)
  (h_bis : EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C) :
-- imply
  dist B D / dist D C = dist A B / dist A C := by
-- proof
  apply MetaMathlibExt.angle_bisector_theorem_general A B C D h_tri h_bet h_bis

/--
[angle_bisector_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/AngleBisector.lean)
-/
@[path]
private lemma angle_bisector_theorem_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
  {A B C D : P}
-- given
  (h_tri : AffineIndependent ℝ (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C))
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hAD : A ≠ D)
  (h_bet : Sbtw ℝ B D C)
  (h_bis : EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C) :
-- imply
  dist B D / dist D C = dist A B / dist A C := by
-- proof
  apply MetaMathlibExt.angle_bisector_theorem A B C D h_tri hAB hAC hAD h_bet h_bis

/--
[angle_bisector_converse_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/AngleBisector.lean)
-/
@[path]
private lemma angle_bisector_converse_general_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
  {A B C D : P}
-- given
  (h_tri : AffineIndependent ℝ (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C))
  (h_bet : Wbtw ℝ B D C)
  (h_ratio : dist B D / dist D C = dist A B / dist A C) :
-- imply
  EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C := by
-- proof
  apply MetaMathlibExt.angle_bisector_converse_general A B C D h_tri h_bet h_ratio

/--
[angle_bisector_converse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/AngleBisector.lean)
-/
@[path]
private lemma angle_bisector_converse_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
  {A B C D : P}
-- given
  (h_tri : AffineIndependent ℝ (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C))
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hAD : A ≠ D)
  (h_bet : Wbtw ℝ B D C)
  (h_ratio : dist B D / dist D C = dist A B / dist A C) :
-- imply
  EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C := by
-- proof
  apply MetaMathlibExt.angle_bisector_converse A B C D h_tri hAB hAC hAD h_bet h_ratio


-- created on 2026-10-20
