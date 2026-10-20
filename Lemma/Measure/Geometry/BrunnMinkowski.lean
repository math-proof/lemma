import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Geometry.BrunnMinkowski
open MeasureTheory
open scoped Pointwise ENNReal
open scoped Pointwise
open MathlibExt.MeasureTheory.Geometry.BrunnMinkowskiWanted


/--
[brunn_minkowski](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BrunnMinkowski.lean)
-/
@[path]
private lemma brunn_minkowski_eq
  {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))] [BorelSpace (EuclideanSpace ℝ (Fin n))]
  {A B : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hn : 0 < n)
  (hA : IsCompact A)
  (hAne : A.Nonempty)
  (hB : IsCompact B)
  (hBne : B.Nonempty) :
-- imply
  ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) ((A + B)))
    ((1 : ℝ) / (n : ℝ)) ≥
    ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) A)
    ((1 : ℝ) / (n : ℝ)) +
    ENNReal.rpow ((volume : Measure (EuclideanSpace ℝ (Fin n))) B)
    ((1 : ℝ) / (n : ℝ)) := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BrunnMinkowskiWanted.brunn_minkowski hn hA hAne hB hBne


-- created on 2026-10-20
