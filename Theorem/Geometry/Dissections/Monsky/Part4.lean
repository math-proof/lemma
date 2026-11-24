module
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Convex.BetweenList
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Side
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Theorem.MeasureTheory.Measure.Lebesgue.TriangleArea.Part3
public import Theorem.Measure.Lebesgue.TriangleArea
public import Def.Geometry.Dissections.Monsky.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/
namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

lemma monsky_faceInteriorParam_spec
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r : ℝ} (hr : r ∈ monskyFaceInteriorParams T htriangle f) :
    r ∈ Set.Ioo (0 : ℝ) 1 ∧
      AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f) r ∈
        monskyNodes T htriangle := by
  classical
  rw [monskyFaceInteriorParams, Finset.mem_image] at hr
  obtain ⟨x, hx, hr⟩ := hr
  obtain ⟨hxnode, hxopen⟩ := Finset.mem_filter.mp hx
  rw [openSegment_eq_image_lineMap] at hxopen
  obtain ⟨s, hs, hsx⟩ := hxopen
  have hinj := AffineMap.lineMap_injective ℝ
    (monsky_face_endpoints_ne T htriangle hcard hvolume f)
  have hinv : Function.invFun
      (AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)) x = s := by
    rw [← hsx]
    exact Function.leftInverse_invFun hinj s
  have hrs : r = s := hr.symm.trans hinv
  constructor
  · rwa [hrs]
  · rw [hrs, hsx]
    exact hxnode

end MetaMathlibExt
