import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.Routh
open MetaMathlibExt


/--
[routh](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Routh.lean)
-/
@[path]
private lemma routh_eq
  :
-- imply
  ∀ (A B C D E F P Q R : EuclideanSpace ℝ (Fin 2)) (x y z : ℝ),
    0 < x →
    0 < y →
    0 < z →
    x * y * z ≠ 1 →
    MeasureTheory.volume (convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) ≠ 0 →
    D = (x / (x + 1)) • B + (1 / (x + 1)) • C →
    E = (1 / (y + 1)) • A + (y / (y + 1)) • C →
    F = (z / (z + 1)) • A + (1 / (z + 1)) • B →
    P ∈ convexHull ℝ ({B, E} : Set (EuclideanSpace ℝ (Fin 2))) →
    P ∈ convexHull ℝ ({C, F} : Set (EuclideanSpace ℝ (Fin 2))) →
    Q ∈ convexHull ℝ ({C, F} : Set (EuclideanSpace ℝ (Fin 2))) →
    Q ∈ convexHull ℝ ({A, D} : Set (EuclideanSpace ℝ (Fin 2))) →
    R ∈ convexHull ℝ ({A, D} : Set (EuclideanSpace ℝ (Fin 2))) →
    R ∈ convexHull ℝ ({B, E} : Set (EuclideanSpace ℝ (Fin 2))) →
    (MeasureTheory.volume (convexHull ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))).toReal =
    ((x * y * z - 1) ^ 2 / ((x * y + y + 1) * (y * z + z + 1) * (z * x + x + 1))) *
    (MeasureTheory.volume (convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))).toReal := by
-- proof
  apply MetaMathlibExt.routh


-- created on 2026-10-20
