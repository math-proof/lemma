import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.MiquelTheorem
open scoped EuclideanSpace
open MetaMathlibExt


/--
[miquel_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/MiquelTheorem.lean)
-/
@[path]
private lemma miquel_theorem_eq
  {A B C D E F O1 O2 O3 : EuclideanSpace ℝ (Fin 2)}
  {r1 r2 r3 : ℝ}
-- given
  (hTri : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
  (hD : D ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))))
  (hE : E ∈ affineSpan ℝ ({C, A} : Set (EuclideanSpace ℝ (Fin 2))))
  (hF : F ∈ affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))))
  (hDB : D ≠ B)
  (hDC : D ≠ C)
  (hEC : E ≠ C)
  (hEA : E ≠ A)
  (hFA : F ≠ A)
  (hFB : F ≠ B)
  (hAEF : A ∈ Metric.sphere O1 r1 ∧ E ∈ Metric.sphere O1 r1 ∧ F ∈ Metric.sphere O1 r1)
  (hBFD : B ∈ Metric.sphere O2 r2 ∧ F ∈ Metric.sphere O2 r2 ∧ D ∈ Metric.sphere O2 r2)
  (hCDE : C ∈ Metric.sphere O3 r3 ∧ D ∈ Metric.sphere O3 r3 ∧ E ∈ Metric.sphere O3 r3) :
-- imply
  ∃ M, M ∈ Metric.sphere O1 r1 ∧ M ∈ Metric.sphere O2 r2 ∧ M ∈ Metric.sphere O3 r3 := by
-- proof
  apply MetaMathlibExt.miquel_theorem A B C D E F hTri hD hE hF hDB hDC hEC hEA hFA hFB O1 O2 O3 r1 r2 r3 hAEF hBFD hCDE


-- created on 2026-10-20
