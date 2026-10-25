/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.BetweenList
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Side
import Mathlib.RingTheory.Valuation.LocalSubring
import Theorem.MeasureTheory.Measure.Lebesgue.TriangleArea.Part3
import Lemma.Measure.Lebesgue.TriangleArea
import Notation.Geometry.Dissections.Monsky
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma monsky_affineIndependent_of_det_ne_zero
    (a b c : EuclideanSpace ℝ (Fin 2))
    (hdet : (a - c).ofLp 0 * (b - c).ofLp 1 -
      (a - c).ofLp 1 * (b - c).ofLp 0 ≠ 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcollinear
  obtain ⟨p, v, hp⟩ :=
    (collinear_iff_exists_forall_eq_smul_vadd
      ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))).1 hcollinear
  obtain ⟨ra, hra⟩ := hp a (by simp)
  obtain ⟨rb, hrb⟩ := hp b (by simp)
  obtain ⟨rc, hrc⟩ := hp c (by simp)
  apply hdet
  rw [hra, hrb, hrc]
  simp only [vadd_eq_add, add_sub_add_right_eq_sub, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

lemma monsky_exists_vertices
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (t : ↑T) :
    ∃ p : Fin 3 → EuclideanSpace ℝ (Fin 2),
      t.1 = convexHull ℝ (Set.range p) := by
  obtain ⟨a, b, c, habc⟩ := htriangle t.1 t.2
  refine ⟨![a, b, c], ?_⟩
  rw [habc]
  congr 1
  ext x
  simp [Matrix.range_cons]
  tauto

end MetaMathlibExt
