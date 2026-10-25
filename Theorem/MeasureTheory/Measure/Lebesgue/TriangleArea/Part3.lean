/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Def.MeasureTheory.Measure.Lebesgue.TriangleArea.Part2
/-!
# Areas of triangles in the Euclidean plane

This file proves the determinant formula for the area of a planar triangle and computes the
volume of the closed unit square.
-/


namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma mem_diagonal_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ diagonal ↔
      ((euclideanPlaneBasis).toBasis.repr x) 0 +
        ((euclideanPlaneBasis).toBasis.repr x) 1 = 1 := by
  rw [diagonal, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub,
    map_sub, sub_eq_zero]
  change (euclideanPlaneBasis).toBasis.sumCoords x =
      (euclideanPlaneBasis).toBasis.sumCoords ((euclideanPlaneBasis).toBasis 0) ↔ _
  rw [Module.Basis.sumCoords_self_apply]
  classical
  change (((euclideanPlaneBasis).toBasis.repr x).sum fun _ ↦ id) = 1 ↔ _
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

lemma diagonal_ne_top : diagonal ≠ ⊤ := by
  intro htop
  have hz : (0 : EuclideanSpace ℝ (Fin 2)) ∈ diagonal := by
    rw [htop]
    trivial
  rw [mem_diagonal_iff] at hz
  simp at hz

lemma triangle_inter_reflect_subset_diagonal :
    standardTriangle ∩ reflect '' standardTriangle ⊆ diagonal := by
  rintro x ⟨hx, hrx⟩
  rw [standardTriangle, mem_standardTriangle_iff] at hx
  rw [mem_reflectedTriangle_iff] at hrx
  exact (mem_diagonal_iff x).2 (le_antisymm hx.2.2 hrx.2.2)

lemma volume_triangle_inter_reflect :
    volume (standardTriangle ∩ reflect '' standardTriangle) = 0 := by
  exact measure_mono_null triangle_inter_reflect_subset_diagonal
    (volume.addHaar_affineSubspace diagonal diagonal_ne_top)

lemma reflect_image_eq_preimage :
    reflect '' standardTriangle = reflect ⁻¹' standardTriangle := by
  ext x
  exact mem_reflect_image_iff x

lemma reflectedTriangle_measurableSet :
    MeasurableSet (reflect '' standardTriangle) := by
  rw [reflect_image_eq_preimage]
  exact standardTriangle_measurableSet.preimage measurePreserving_reflect.measurable

lemma volume_reflectedTriangle :
    volume (reflect '' standardTriangle) = volume standardTriangle := by
  rw [reflect_image_eq_preimage]
  exact measurePreserving_reflect.measure_preimage
    standardTriangle_measurableSet.nullMeasurableSet

lemma two_volume_standardTriangle :
    volume standardTriangle + volume standardTriangle = 1 := by
  calc
    volume standardTriangle + volume standardTriangle =
        volume standardTriangle +
          volume (reflect '' standardTriangle) := by
      rw [volume_reflectedTriangle]
    _ = volume (standardTriangle ∪ reflect '' standardTriangle) := by
      have hunion := measure_union_add_inter (μ := volume) standardTriangle
        reflectedTriangle_measurableSet
      rw [volume_triangle_inter_reflect, add_zero] at hunion
      exact hunion.symm
    _ = volume (parallelepiped euclideanPlaneBasis) := by
      rw [parallelepiped_eq_union]
    _ = 1 := (euclideanPlaneBasis).volume_parallelepiped

lemma toReal_volume_standardTriangle :
    (volume standardTriangle).toReal = 1 / 2 := by
  have hfinite : volume standardTriangle ≠ ⊤ :=
    ne_of_lt standardTriangle_isCompact.measure_lt_top
  have hre := congrArg ENNReal.toReal two_volume_standardTriangle
  rw [ENNReal.toReal_add hfinite hfinite] at hre
  norm_num at hre ⊢
  linarith

lemma det_constr (u v : EuclideanSpace ℝ (Fin 2)) :
    ((euclideanPlaneBasis).toBasis.constr ℝ
      (![u, v] : Fin 2 → EuclideanSpace ℝ (Fin 2))).det =
      u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0 := by
  rw [← LinearMap.det_toMatrix (euclideanPlaneBasis).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]
  ring

lemma image_standardTriangle (u v : EuclideanSpace ℝ (Fin 2)) :
    ((euclideanPlaneBasis).toBasis.constr ℝ
      (![u, v] : Fin 2 → EuclideanSpace ℝ (Fin 2))) '' standardTriangle =
      convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [standardTriangle, LinearMap.image_convexHull]
  congr 1
  simp

lemma translate_triangle (a b c : EuclideanSpace ℝ (Fin 2)) :
    (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 2)) a).toAffineMap ''
        convexHull ℝ ({0, b - a, c - a} : Set (EuclideanSpace ℝ (Fin 2))) =
      convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [AffineMap.image_convexHull]
  congr 1
  simp [AffineEquiv.constVAdd_apply]

lemma volume_translate (a : EuclideanSpace ℝ (Fin 2))
    (s : Set (EuclideanSpace ℝ (Fin 2))) (hs : NullMeasurableSet s volume) :
    volume ((fun x ↦ a + x) '' s) = volume s := by
  have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) ↦ -a + x)
      volume volume := measurePreserving_add_left volume (-a)
  have hset : (fun x : EuclideanSpace ℝ (Fin 2) ↦ -a + x) ⁻¹' s =
      (fun x ↦ a + x) '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨-a + x, hx, by abel_nf⟩
    · rintro ⟨y, hy, rfl⟩
      change -a + (a + y) ∈ s
      simpa only [neg_add_cancel_left] using hy
  have hpre := hmp.measure_preimage hs
  rwa [hset] at hpre

lemma volume_triangle (a b c : EuclideanSpace ℝ (Fin 2)) :
    volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) =
      ENNReal.ofReal |(b - a).ofLp 0 * (c - a).ofLp 1 -
        (b - a).ofLp 1 * (c - a).ofLp 0| * volume standardTriangle := by
  let u := b - a
  let v := c - a
  let f := (euclideanPlaneBasis).toBasis.constr ℝ
    (![u, v] : Fin 2 → EuclideanSpace ℝ (Fin 2))
  have hcompact : IsCompact
      (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) :=
    (by simp : Set.Finite
      ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))).isCompact_convexHull ℝ
  have hmeas : NullMeasurableSet
      (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) volume :=
    hcompact.isClosed.measurableSet.nullMeasurableSet
  calc
    volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) =
        volume ((fun x ↦ a + x) ''
          convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [show u = b - a from rfl, show v = c - a from rfl,
        ← translate_triangle a b c]
      rfl
    _ = volume (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) :=
      volume_translate a _ hmeas
    _ = volume (f '' standardTriangle) := by
      simp only [f, image_standardTriangle]
    _ = ENNReal.ofReal |f.det| * volume standardTriangle := by
      rw [Measure.addHaar_image_linearMap]
    _ = _ := by
      simp only [f, det_constr, u, v]

/-- The Euclidean area of a planar triangle is half the absolute determinant of its two
edge vectors. -/
theorem _root_.MeasureTheory.toReal_volume_convexHull_triangle
    (a b c : EuclideanSpace ℝ (Fin 2)) :
    (volume (convexHull ℝ
      ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))))).toReal =
      |(b - a).ofLp 0 * (c - a).ofLp 1 - (b - a).ofLp 1 * (c - a).ofLp 0| / 2 := by
  rw [volume_triangle, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), toReal_volume_standardTriangle]
  ring

end MetaMathlibExt
