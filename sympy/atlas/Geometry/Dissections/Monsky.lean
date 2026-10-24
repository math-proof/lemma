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
import sympy.atlas.MeasureTheory.Measure.Lebesgue.TriangleArea
import Lemma.Measure.Lebesgue.TriangleArea
/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/

namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

private lemma monsky_affineIndependent_of_det_ne_zero
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

private lemma monsky_exists_vertices
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

private noncomputable def monskyVertices
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (t : ↑T) :
    Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  Classical.choose (monsky_exists_vertices T htriangle t)

private lemma monsky_vertices_spec
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (t : ↑T) :
    t.1 = convexHull ℝ (Set.range (monskyVertices T htriangle t)) :=
  Classical.choose_spec (monsky_exists_vertices T htriangle t)

private lemma monsky_vertices_independent
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) (t : ↑T) :
    AffineIndependent ℝ (monskyVertices T htriangle t) := by
  let p := monskyVertices T htriangle t
  have hp : t.1 = convexHull ℝ (Set.range p) := monsky_vertices_spec T htriangle t
  have hrange : Set.range p = {p 0, p 1, p 2} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hv := hvolume t.1 t.2
  rw [hp, hrange, MeasureTheory.toReal_volume_convexHull_triangle] at hv
  have hcyclic :
      (p 1 - p 0).ofLp 0 * (p 2 - p 0).ofLp 1 -
          (p 1 - p 0).ofLp 1 * (p 2 - p 0).ofLp 0 =
        (p 0 - p 2).ofLp 0 * (p 1 - p 2).ofLp 1 -
          (p 0 - p 2).ofLp 1 * (p 1 - p 2).ofLp 0 := by
    simp only [PiLp.sub_apply]
    ring
  have hdet : (p 0 - p 2).ofLp 0 * (p 1 - p 2).ofLp 1 -
      (p 0 - p 2).ofLp 1 * (p 1 - p 2).ofLp 0 ≠ 0 := by
    intro hzero
    rw [hcyclic, hzero, abs_zero, zero_div] at hv
    have hpos : (0 : ℝ) < 1 / (T.card : ℝ) := by
      positivity
    linarith
  have hi := monsky_affineIndependent_of_det_ne_zero (p 0) (p 1) (p 2) hdet
  have hpvec : ![p 0, p 1, p 2] = p := by
    funext i
    fin_cases i <;> rfl
  rw [hpvec] at hi
  exact hi

private noncomputable def monskyTriangleBasis
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) (t : ↑T) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) := by
  let s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 :=
    ⟨monskyVertices T htriangle t, monsky_vertices_independent T htriangle hcard hvolume t⟩
  exact ⟨s.points, s.independent, s.affineSpan_eq_top (by simp)⟩

private noncomputable def monskySquareCorner (i : Fin 4) :
    EuclideanSpace ℝ (Fin 2) :=
  ![0, euclideanPlaneBasis 0, euclideanPlaneBasis 0 + euclideanPlaneBasis 1,
    euclideanPlaneBasis 1] i

private abbrev MonskyFace
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))) := (↑T × Fin 3) ⊕ Fin 4

private noncomputable def monskyFaceLeft
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : MonskyFace T → EuclideanSpace ℝ (Fin 2)
  | .inl (t, i) => monskyVertices T htriangle t (i + 1)
  | .inr i => monskySquareCorner i

private noncomputable def monskyFaceRight
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : MonskyFace T → EuclideanSpace ℝ (Fin 2)
  | .inl (t, i) => monskyVertices T htriangle t (i + 2)
  | .inr i => monskySquareCorner (i + 1)

private noncomputable def monskyCoordinate (i : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  (EuclideanSpace.projₗ i).toAffineMap

private noncomputable def monskySquareSideForm (i : Fin 4) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  ![monskyCoordinate 1,
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) 1 - monskyCoordinate 0,
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) 1 - monskyCoordinate 1,
    monskyCoordinate 0] i

private noncomputable def monskyFaceForm
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    MonskyFace T → EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ
  | .inl (t, i) => (monskyTriangleBasis T htriangle hcard hvolume t).coord i
  | .inr i => monskySquareSideForm i

private lemma monsky_face_endpoints_ne
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : monskyFaceLeft T htriangle f ≠ monskyFaceRight T htriangle f := by
  rcases f with ⟨t, i⟩ | i
  · apply (monsky_vertices_independent T htriangle hcard hvolume t).injective.ne
    fin_omega
  · fin_cases i
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 0) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 1) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 0) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 1) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this

private lemma monsky_mem_tile_iff_faceForms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (t : ↑T) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ t.1 ↔ ∀ i : Fin 3, 0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x := by
  let b := monskyTriangleBasis T htriangle hcard hvolume t
  have hrange : Set.range (monskyVertices T htriangle t) = Set.range b := by
    ext y
    simp only [Set.mem_range]
    constructor <;> rintro ⟨i, rfl⟩
    · exact ⟨i, (monsky_triangleBasis_apply T htriangle hcard hvolume t i).symm⟩
    · exact ⟨i, monsky_triangleBasis_apply T htriangle hcard hvolume t i⟩
  rw [monsky_vertices_spec T htriangle t, hrange, b.convexHull_eq_nonneg_coord]
  rfl

private lemma monsky_mem_interior_tile_iff_faceForms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (t : ↑T) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ interior t.1 ↔
      ∀ i : Fin 3, 0 < monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x := by
  let b := monskyTriangleBasis T htriangle hcard hvolume t
  have hrange : Set.range (monskyVertices T htriangle t) = Set.range b := by
    ext y
    simp only [Set.mem_range]
    constructor <;> rintro ⟨i, rfl⟩
    · exact ⟨i, (monsky_triangleBasis_apply T htriangle hcard hvolume t i).symm⟩
    · exact ⟨i, monsky_triangleBasis_apply T htriangle hcard hvolume t i⟩
  rw [monsky_vertices_spec T htriangle t, hrange, b.interior_convexHull]
  rfl

private noncomputable def monskyFaceLine
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  affineSpan ℝ
    ({monskyFaceLeft T htriangle f, monskyFaceRight T htriangle f} :
      Set (EuclideanSpace ℝ (Fin 2)))

private noncomputable def monskyIntersectionPoint
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f g : MonskyFace T) :
    EuclideanSpace ℝ (Fin 2) := by
  classical
  exact if h : ((monskyFaceLine T htriangle f : Set (EuclideanSpace ℝ (Fin 2))) ∩
      monskyFaceLine T htriangle g).Nonempty then Classical.choose h
    else monskyFaceLeft T htriangle f

private noncomputable def monskyNodes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : Finset (EuclideanSpace ℝ (Fin 2)) := by
  classical
  exact
    (Finset.univ.image (monskyFaceLeft T htriangle) ∪
      Finset.univ.image (monskyFaceRight T htriangle)) ∪
      Finset.univ.biUnion fun f : MonskyFace T ↦
        Finset.univ.image fun g : MonskyFace T ↦ monskyIntersectionPoint T htriangle f g

private noncomputable def monskyFaceInteriorParams
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) : Finset ℝ := by
  classical
  exact ((monskyNodes T htriangle).filter fun x ↦
      x ∈ openSegment ℝ (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)).image
    (Function.invFun (AffineMap.lineMap
      (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)))

private lemma monsky_faceInteriorParam_spec
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

private noncomputable def monskyFaceParamList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) : List ℝ :=
  0 :: (monskyFaceInteriorParams T htriangle f).sort (fun a b ↦ a ≤ b) ++ [1]

private lemma monsky_faceParamList_sorted
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFaceParamList T htriangle f).SortedLT := by
  let l := (monskyFaceInteriorParams T htriangle f).sort (fun a b ↦ a ≤ b)
  have hl : l.SortedLT := Finset.sortedLT_sort _
  have hmem : ∀ r ∈ l, r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
      ((Finset.mem_sort _).1 hr)).1
  change ((0 :: l) ++ [1]).SortedLT
  rw [List.sortedLT_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.sortedLT_cons]
    exact ⟨fun r hr ↦ (hmem r hr).1, hl⟩
  · rw [List.sortedLT_iff_pairwise]
    exact List.pairwise_singleton (· < ·) 1
  · intro r hr q hq
    have hq1 : q = 1 := List.mem_singleton.mp hq
    subst q
    rcases List.mem_cons.mp hr with rfl | hr
    · norm_num
    · exact (hmem r hr).2

private noncomputable def monskyFacePointList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    List (EuclideanSpace ℝ (Fin 2)) :=
  (monskyFaceParamList T htriangle f).map
    (AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f))

private noncomputable def monskyFaceAtomList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    List (Sym2 (EuclideanSpace ℝ (Fin 2))) :=
  (monskyFacePointList T htriangle f).consecutivePairs.map fun e ↦ s(e.1, e.2)

private noncomputable def monskyAtoms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : Finset (Sym2 (EuclideanSpace ℝ (Fin 2))) := by
  classical
  exact Finset.univ.biUnion fun f : MonskyFace T ↦
    (monskyFaceAtomList T htriangle f).toFinset

private noncomputable def monskyAtomMidpoint :
    Sym2 (EuclideanSpace ℝ (Fin 2)) → EuclideanSpace ℝ (Fin 2) :=
  Sym2.lift ⟨fun a b ↦ midpoint ℝ a b, fun a b ↦ midpoint_comm a b⟩

@[simp] private lemma monsky_atomMidpoint_mk
    (a b : EuclideanSpace ℝ (Fin 2)) :
    monskyAtomMidpoint s(a, b) = midpoint ℝ a b := by
  rfl

/-- The mod-two edge weight used in the Sperner count.  It detects an edge whose endpoint
colours are `0` and `2`. -/
private def monskyEdgeWeight (i j : Fin 3) : ZMod 2 :=
  if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 0

private def monskyPathWeight : List (Fin 3) → ZMod 2
  | [] => 0
  | [_] => 0
  | a :: b :: l => monskyEdgeWeight a b + monskyPathWeight (b :: l)

private lemma monsky_mem_faceParamList_bounds
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r : ℝ} (hr : r ∈ monskyFaceParamList T htriangle f) :
    0 ≤ r ∧ r ≤ 1 := by
  rw [monskyFaceParamList, List.mem_append] at hr
  rcases hr with hr | hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · norm_num
    · have hir := (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
        ((Finset.mem_sort _).1 hr)).1
      exact ⟨hir.1.le, hir.2.le⟩
  · have hr1 : r = 1 := List.mem_singleton.mp hr
    subst r
    norm_num

private lemma monsky_atomMidpoint_mem_openSegment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (he : e ∈ monskyFaceAtomList T htriangle f) :
    monskyAtomMidpoint e ∈
      openSegment ℝ (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f) := by
  obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 he
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hr := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_fst_mem_of_mem_consecutivePairs hrq)
  have hq := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_snd_mem_of_mem_consecutivePairs hrq)
  rw [openSegment_eq_image_lineMap]
  refine ⟨midpoint ℝ r q, ?_, ?_⟩
  · simp only [midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    constructor <;> norm_num <;> linarith
  · exact (monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq).symm

private lemma monsky_atomMidpoint_not_mem_distinct_faceLine
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f g : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (he : e ∈ monskyFaceAtomList T htriangle f)
    (hfg : monskyFaceLine T htriangle f ≠ monskyFaceLine T htriangle g) :
    monskyAtomMidpoint e ∉ monskyFaceLine T htriangle g := by
  intro hmg
  obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 he
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
  let u := midpoint ℝ r q
  have hm : monskyAtomMidpoint e = L u :=
    monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq
  have hmf : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle f := by
    rw [hm, monskyFaceLine]
    exact AffineMap.lineMap_mem_affineSpan_pair u _ _
  have hinter : monskyIntersectionPoint T htriangle f g = monskyAtomMidpoint e :=
    monsky_intersectionPoint_eq_of_mem T htriangle f g hfg hmf hmg
  have hmnode : monskyAtomMidpoint e ∈ monskyNodes T htriangle := by
    rw [← hinter]
    exact monsky_intersectionPoint_mem_nodes T htriangle f g
  have hmopen := monsky_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e he
  have huparam : u ∈ monskyFaceInteriorParams T htriangle f := by
    have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hmnode hmopen
    have hLinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hinvu : Function.invFun L (monskyAtomMidpoint e) = u := by
      rw [hm]
      exact Function.leftInverse_invFun hLinj u
    rwa [hinvu] at hinv
  have hulist : u ∈ monskyFaceParamList T htriangle f := by
    rw [monskyFaceParamList, List.mem_append]
    left
    exact List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 huparam)
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hubetween : r < u ∧ u < q := by
    simp only [u, midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    constructor <;> norm_num <;> linarith
  exact monsky_not_between_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq hulist hubetween

private lemma monsky_lineMap_mem_nodes_of_mem_paramList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r : ℝ} (hr : r ∈ monskyFaceParamList T htriangle f) :
    AffineMap.lineMap (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f) r ∈ monskyNodes T htriangle := by
  rw [monskyFaceParamList, List.mem_append] at hr
  rcases hr with hr | hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · simpa using monsky_faceLeft_mem_nodes T htriangle f
    · exact (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
        ((Finset.mem_sort _).1 hr)).2
  · have hr1 : r = 1 := List.mem_singleton.mp hr
    subst r
    simpa using monsky_faceRight_mem_nodes T htriangle f

private lemma monsky_mem_pointList_of_mem_nodes_of_mem_segment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {x : EuclideanSpace ℝ (Fin 2)}
    (hnode : x ∈ monskyNodes T htriangle)
    (hsegment : x ∈ segment ℝ (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f)) :
    x ∈ monskyFacePointList T htriangle f := by
  rw [segment_eq_image_lineMap] at hsegment
  obtain ⟨r, hr, hrx⟩ := hsegment
  have hparam : r ∈ monskyFaceParamList T htriangle f := by
    rcases eq_or_lt_of_le hr.1 with rfl | hr0
    · rw [monskyFaceParamList, List.mem_append]
      exact Or.inl (by simp)
    · rcases eq_or_lt_of_le hr.2 with rfl | hr1
      · rw [monskyFaceParamList, List.mem_append]
        exact Or.inr (by simp)
      · have hopen : x ∈ openSegment ℝ (monskyFaceLeft T htriangle f)
            (monskyFaceRight T htriangle f) := by
          rw [openSegment_eq_image_lineMap]
          exact ⟨r, ⟨hr0, hr1⟩, hrx⟩
        have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hnode hopen
        have hinj := AffineMap.lineMap_injective ℝ
          (monsky_face_endpoints_ne T htriangle hcard hvolume f)
        have hinvr : Function.invFun (AffineMap.lineMap
            (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)) x = r := by
          rw [← hrx]
          exact Function.leftInverse_invFun hinj r
        rw [hinvr] at hinv
        rw [monskyFaceParamList, List.mem_append]
        exact Or.inl (List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 hinv))
  rw [monskyFacePointList, List.mem_map]
  exact ⟨r, hparam, hrx⟩

private lemma monsky_no_node_mem_openSegment_of_consecutive
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r q : ℝ}
    (hrq : (r, q) ∈ (monskyFaceParamList T htriangle f).consecutivePairs)
    {x : EuclideanSpace ℝ (Fin 2)} (hnode : x ∈ monskyNodes T htriangle) :
    x ∉ openSegment ℝ
      (AffineMap.lineMap (monskyFaceLeft T htriangle f)
        (monskyFaceRight T htriangle f) r)
      (AffineMap.lineMap (monskyFaceLeft T htriangle f)
        (monskyFaceRight T htriangle f) q) := by
  intro hxopen
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
  rw [openSegment_eq_image_lineMap] at hxopen
  obtain ⟨t, ht, htx⟩ := hxopen
  let u := AffineMap.lineMap r q t
  have hLux : L u = x := by
    change L (AffineMap.lineMap r q t) = x
    rw [L.apply_lineMap, htx]
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hubetween : r < u ∧ u < q := by
    simp only [u, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    constructor <;> nlinarith [ht.1, ht.2]
  have hrbounds := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_fst_mem_of_mem_consecutivePairs hrq)
  have hqbounds := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_snd_mem_of_mem_consecutivePairs hrq)
  have huopen : x ∈ openSegment ℝ (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f) := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨u, ⟨hrbounds.1.trans_lt hubetween.1,
      hubetween.2.trans_le hqbounds.2⟩, hLux⟩
  have huparam : u ∈ monskyFaceInteriorParams T htriangle f := by
    have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hnode huopen
    have hinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hinvu : Function.invFun L x = u := by
      rw [← hLux]
      exact Function.leftInverse_invFun hinj u
    rwa [hinvu] at hinv
  have hulist : u ∈ monskyFaceParamList T htriangle f := by
    rw [monskyFaceParamList, List.mem_append]
    exact Or.inl (List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 huparam))
  exact monsky_not_between_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq hulist hubetween

private lemma monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (g : MonskyFace T) :
    e ∈ monskyFaceAtomList T htriangle g ↔
      monskyAtomMidpoint e ∈
        openSegment ℝ (monskyFaceLeft T htriangle g) (monskyFaceRight T htriangle g) := by
  constructor
  · exact monsky_atomMidpoint_mem_openSegment T htriangle hcard hvolume g e
  · intro hmopen
    obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 hef
    let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
    let G : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (monskyFaceLeft T htriangle g) (monskyFaceRight T htriangle g)
    have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
      (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
    have hm : monskyAtomMidpoint e = L (midpoint ℝ r q) :=
      monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq
    rw [openSegment_eq_image_lineMap] at hmopen
    obtain ⟨t, ht, htm⟩ := hmopen
    have hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g := by
      rw [← htm, monskyFaceLine]
      exact AffineMap.lineMap_mem_affineSpan_pair t _ _
    have hline : monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
      by_contra hne
      exact monsky_atomMidpoint_not_mem_distinct_faceLine
        T htriangle hcard hvolume f g e hef hne hmg
    have hgleft : monskyFaceLeft T htriangle g ∈ monskyFaceLine T htriangle g := by
      rw [monskyFaceLine]
      exact left_mem_affineSpan_pair ℝ _ _
    have hgright : monskyFaceRight T htriangle g ∈ monskyFaceLine T htriangle g := by
      rw [monskyFaceLine]
      exact right_mem_affineSpan_pair ℝ _ _
    have hgleft' : monskyFaceLeft T htriangle g ∈ monskyFaceLine T htriangle f := by
      rwa [hline]
    have hgright' : monskyFaceRight T htriangle g ∈ monskyFaceLine T htriangle f := by
      rwa [hline]
    rw [monskyFaceLine, mem_affineSpan_pair_iff_exists_lineMap_eq] at hgleft' hgright'
    obtain ⟨a, ha⟩ := hgleft'
    obtain ⟨b, hb⟩ := hgright'
    have hLinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hscalar : midpoint ℝ r q = AffineMap.lineMap a b t := by
      apply hLinj
      calc
        L (midpoint ℝ r q) = monskyAtomMidpoint e := hm.symm
        _ = G t := htm.symm
        _ = AffineMap.lineMap (L a) (L b) t := by rw [ha, hb]
        _ = L (AffineMap.lineMap a b t) := (L.apply_lineMap a b t).symm
    have hleftNode : monskyFaceLeft T htriangle g ∈ monskyNodes T htriangle :=
      monsky_faceLeft_mem_nodes T htriangle g
    have hrightNode : monskyFaceRight T htriangle g ∈ monskyNodes T htriangle :=
      monsky_faceRight_mem_nodes T htriangle g
    have haout : a ∉ Set.Ioo r q := by
      intro hain
      apply monsky_no_node_mem_openSegment_of_consecutive
        T htriangle hcard hvolume f hrq hleftNode
      rw [← image_openSegment ℝ L r q, openSegment_eq_Ioo hrqlt]
      exact ⟨a, hain, ha⟩
    have hbout : b ∉ Set.Ioo r q := by
      intro hbin
      apply monsky_no_node_mem_openSegment_of_consecutive
        T htriangle hcard hvolume f hrq hrightNode
      rw [← image_openSegment ℝ L r q, openSegment_eq_Ioo hrqlt]
      exact ⟨b, hbin, hb⟩
    have henclose := monsky_scalar_segment_enclosure hrqlt ht hscalar haout hbout
    have hrseg : r ∈ segment ℝ a b := by
      rcases henclose with henclose | henclose
      · exact Icc_subset_segment ⟨henclose.1, hrqlt.le.trans henclose.2⟩
      · rw [segment_symm]
        exact Icc_subset_segment ⟨henclose.1, hrqlt.le.trans henclose.2⟩
    have hqseg : q ∈ segment ℝ a b := by
      rcases henclose with henclose | henclose
      · exact Icc_subset_segment ⟨henclose.1.trans hrqlt.le, henclose.2⟩
      · rw [segment_symm]
        exact Icc_subset_segment ⟨henclose.1.trans hrqlt.le, henclose.2⟩
    have hLrseg : L r ∈ segment ℝ (monskyFaceLeft T htriangle g)
        (monskyFaceRight T htriangle g) := by
      rw [← ha, ← hb, ← image_segment ℝ L a b]
      exact ⟨r, hrseg, rfl⟩
    have hLqseg : L q ∈ segment ℝ (monskyFaceLeft T htriangle g)
        (monskyFaceRight T htriangle g) := by
      rw [← ha, ← hb, ← image_segment ℝ L a b]
      exact ⟨q, hqseg, rfl⟩
    have hrmem := monsky_fst_mem_of_mem_consecutivePairs hrq
    have hqmem := monsky_snd_mem_of_mem_consecutivePairs hrq
    have hLrNode := monsky_lineMap_mem_nodes_of_mem_paramList
      T htriangle hcard hvolume f hrmem
    have hLqNode := monsky_lineMap_mem_nodes_of_mem_paramList
      T htriangle hcard hvolume f hqmem
    have hLrPoint := monsky_mem_pointList_of_mem_nodes_of_mem_segment
      T htriangle hcard hvolume g hLrNode hLrseg
    have hLqPoint := monsky_mem_pointList_of_mem_nodes_of_mem_segment
      T htriangle hcard hvolume g hLqNode hLqseg
    rw [monskyFacePointList, List.mem_map] at hLrPoint hLqPoint
    obtain ⟨r', hr'mem, hr'eq⟩ := hLrPoint
    obtain ⟨q', hq'mem, hq'eq⟩ := hLqPoint
    have hGinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume g)
    have hrqne : L r ≠ L q := hLinj.ne hrqlt.ne
    have hr'q'ne : r' ≠ q' := by
      intro h
      apply hrqne
      rw [← hr'eq, ← hq'eq, h]
    rcases lt_or_gt_of_ne hr'q'ne with hr'q' | hq'r'
    · have hno : ∀ u ∈ monskyFaceParamList T htriangle g,
          ¬(r' < u ∧ u < q') := by
        intro u hu hubetween
        have huNode := monsky_lineMap_mem_nodes_of_mem_paramList
          T htriangle hcard hvolume g hu
        apply monsky_no_node_mem_openSegment_of_consecutive
          T htriangle hcard hvolume f hrq huNode
        rw [← hr'eq, ← hq'eq, ← image_openSegment ℝ G r' q',
          openSegment_eq_Ioo hr'q']
        exact ⟨u, hubetween, rfl⟩
      have hadj := monsky_mem_consecutivePairs_of_sortedLT
        (monsky_faceParamList_sorted T htriangle hcard hvolume g)
        hr'mem hq'mem hr'q' hno
      apply (monsky_mem_faceAtomList_iff T htriangle g e).2
      refine ⟨r', q', hadj, ?_⟩
      rw [heq, ← hr'eq, ← hq'eq]
    · have hno : ∀ u ∈ monskyFaceParamList T htriangle g,
          ¬(q' < u ∧ u < r') := by
        intro u hu hubetween
        have huNode := monsky_lineMap_mem_nodes_of_mem_paramList
          T htriangle hcard hvolume g hu
        apply monsky_no_node_mem_openSegment_of_consecutive
          T htriangle hcard hvolume f hrq huNode
        rw [← hq'eq, ← hr'eq, openSegment_symm, ← image_openSegment ℝ G q' r',
          openSegment_eq_Ioo hq'r']
        exact ⟨u, hubetween, rfl⟩
      have hadj := monsky_mem_consecutivePairs_of_sortedLT
        (monsky_faceParamList_sorted T htriangle hcard hvolume g)
        hq'mem hr'mem hq'r' hno
      apply (monsky_mem_faceAtomList_iff T htriangle g e).2
      refine ⟨q', r', hadj, ?_⟩
      rw [heq, ← hr'eq, ← hq'eq, Sym2.eq_swap]

private noncomputable def monskyFaceOffPoint
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : MonskyFace T → EuclideanSpace ℝ (Fin 2)
  | .inl (t, i) => monskyVertices T htriangle t i
  | .inr _ => (2 : ℝ)⁻¹ • (euclideanPlaneBasis 0 + euclideanPlaneBasis 1)

private lemma monsky_exists_atom_probes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) :
    ∃ p n : EuclideanSpace ℝ (Fin 2),
      (∀ g : MonskyFace T,
        monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
              monskyFaceForm T htriangle hcard hvolume g p ∧
            0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
              monskyFaceForm T htriangle hcard hvolume g n) ∧
      (∀ g : MonskyFace T,
        monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
          monskyFaceForm T htriangle hcard hvolume g p *
            monskyFaceForm T htriangle hcard hvolume g n < 0) := by
  let m := monskyAtomMidpoint e
  let z := monskyFaceOffPoint T htriangle f
  let probe : ℝ → EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap m z
  have hevent : ∀ᶠ r in nhds (0 : ℝ), ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g m ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g m *
            monskyFaceForm T htriangle hcard hvolume g (probe r) ∧
          0 < monskyFaceForm T htriangle hcard hvolume g m *
            monskyFaceForm T htriangle hcard hvolume g (probe (-r)) := by
    rw [Filter.eventually_all]
    intro g
    by_cases hzero : monskyFaceForm T htriangle hcard hvolume g m = 0
    · exact Filter.Eventually.of_forall fun _ hne ↦ (hne hzero).elim
    · let F := monskyFaceForm T htriangle hcard hvolume g
      have hFcont := monsky_faceForm_continuous T htriangle hcard hvolume g
      have hprobeCont : Continuous probe := AffineMap.lineMap_continuous
      have hnegProbeCont : Continuous (fun r ↦ probe (-r)) :=
        hprobeCont.comp continuous_neg
      have hplusCont : Continuous (fun r ↦ F m * F (probe r)) :=
        continuous_const.mul (hFcont.comp hprobeCont)
      have hminusCont : Continuous (fun r ↦ F m * F (probe (-r))) :=
        continuous_const.mul (hFcont.comp hnegProbeCont)
      have hsquare : 0 < F m * F m := mul_self_pos.mpr hzero
      have hplus0 : 0 < F m * F (probe 0) := by
        simpa [probe] using hsquare
      have hminus0 : 0 < F m * F (probe (-0)) := by
        simpa [probe] using hsquare
      filter_upwards [continuousAt_const.eventually_lt hplusCont.continuousAt hplus0,
        continuousAt_const.eventually_lt hminusCont.continuousAt hminus0] with r hp hn
      exact fun _ ↦ ⟨hp, hn⟩
  obtain ⟨ε, hε, hpreserve⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδdist : dist δ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    dsimp [δ]
    linarith
  have hpreserveδ := hpreserve hδdist
  refine ⟨probe δ, probe (-δ), ?_, ?_⟩
  · simpa only [m] using hpreserveδ
  · intro g hgm
    have hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g :=
      (monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume g (monskyAtomMidpoint e)).2 hgm
    have hline : monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
      by_contra hne
      exact monsky_atomMidpoint_not_mem_distinct_faceLine
        T htriangle hcard hvolume f g e hef hne hmg
    have hznotf : z ∉ monskyFaceLine T htriangle f := by
      intro hzf
      have hz0 := (monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume f z).1 hzf
      exact (ne_of_gt (monsky_faceForm_offPoint_pos
        T htriangle hcard hvolume f)) hz0
    have hznotg : z ∉ monskyFaceLine T htriangle g := by
      rwa [← hline]
    have hgz : monskyFaceForm T htriangle hcard hvolume g z ≠ 0 := by
      intro hzero
      exact hznotg ((monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume g z).2 hzero)
    have hplus : monskyFaceForm T htriangle hcard hvolume g (probe δ) =
        AffineMap.lineMap
          (monskyFaceForm T htriangle hcard hvolume g m)
          (monskyFaceForm T htriangle hcard hvolume g z) δ := by
      exact (monskyFaceForm T htriangle hcard hvolume g).apply_lineMap m z δ
    have hminus : monskyFaceForm T htriangle hcard hvolume g (probe (-δ)) =
        AffineMap.lineMap
          (monskyFaceForm T htriangle hcard hvolume g m)
          (monskyFaceForm T htriangle hcard hvolume g z) (-δ) := by
      exact (monskyFaceForm T htriangle hcard hvolume g).apply_lineMap m z (-δ)
    rw [hplus, hminus]
    have hgm' : monskyFaceForm T htriangle hcard hvolume g m = 0 := by
      simpa only [m] using hgm
    rw [hgm']
    change AffineMap.lineMap 0
        (monskyFaceForm T htriangle hcard hvolume g z) δ *
      AffineMap.lineMap 0
        (monskyFaceForm T htriangle hcard hvolume g z) (-δ) < 0
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
      sub_zero]
    have hprod : δ * monskyFaceForm T htriangle hcard hvolume g z ≠ 0 :=
      mul_ne_zero hδ.ne' hgz
    nlinarith [mul_self_pos.mpr hprod]

private noncomputable def monskyIndicator (P : Prop) : ZMod 2 := by
  classical
  exact if P then 1 else 0

private lemma monsky_faceLine_eq_of_atomMidpoint_mem
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (g : MonskyFace T)
    (hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g) :
    monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
  by_contra hne
  exact monsky_atomMidpoint_not_mem_distinct_faceLine
    T htriangle hcard hvolume f g e hef hne hmg

private lemma monsky_triangle_atom_occ_iff
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (t : ↑T) (i : Fin 3) :
    e ∈ monskyFaceAtomList T htriangle (.inl (t, i)) ↔
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i))
          (monskyAtomMidpoint e) = 0 ∧
        ∀ j, j ≠ i →
          0 < monskyFaceForm T htriangle hcard hvolume (.inl (t, j))
            (monskyAtomMidpoint e) := by
  rw [monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e hef]
  simpa only [monskyFaceLeft, monskyFaceRight, monskyFaceForm,
    monsky_triangleBasis_apply] using
    (monsky_mem_open_affineBasis_face_iff
      (monskyTriangleBasis T htriangle hcard hvolume t) i (monskyAtomMidpoint e))

private lemma monsky_square_atom_occ_iff
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (i : Fin 4) :
    e ∈ monskyFaceAtomList T htriangle (.inr i) ↔
      monskyFaceForm T htriangle hcard hvolume (.inr i) (monskyAtomMidpoint e) = 0 ∧
        ∀ j, j ≠ i →
          0 < monskyFaceForm T htriangle hcard hvolume (.inr j)
            (monskyAtomMidpoint e) := by
  rw [monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e hef]
  simpa only [monskyFaceForm] using
    (monsky_mem_open_square_face_iff T htriangle i (monskyAtomMidpoint e))

private lemma monsky_triangle_atom_unique_zero
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (t : ↑T) (i j : Fin 3)
    (hi : monskyFaceForm T htriangle hcard hvolume (.inl (t, i))
      (monskyAtomMidpoint e) = 0)
    (hj : monskyFaceForm T htriangle hcard hvolume (.inl (t, j))
      (monskyAtomMidpoint e) = 0) : i = j := by
  have hmi := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inl (t, i)) (monskyAtomMidpoint e)).2 hi
  have hmj := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inl (t, j)) (monskyAtomMidpoint e)).2 hj
  have hfi := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inl (t, i)) hmi
  have hfj := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inl (t, j)) hmj
  exact monsky_triangle_faceLine_injective T htriangle hcard hvolume t
    (hfi.symm.trans hfj)

private lemma monsky_square_atom_unique_zero
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (i j : Fin 4)
    (hi : monskyFaceForm T htriangle hcard hvolume (.inr i)
      (monskyAtomMidpoint e) = 0)
    (hj : monskyFaceForm T htriangle hcard hvolume (.inr j)
      (monskyAtomMidpoint e) = 0) : i = j := by
  have hmi := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inr i) (monskyAtomMidpoint e)).2 hi
  have hmj := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inr j) (monskyAtomMidpoint e)).2 hj
  have hfi := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inr i) hmi
  have hfj := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inr j) hmj
  exact monsky_square_faceLine_injective T htriangle hcard hvolume (hfi.symm.trans hfj)

private lemma monsky_triangle_atom_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f)
    (p n : EuclideanSpace ℝ (Fin 2))
    (hstable : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g p ∧
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g n)
    (hflip : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
        monskyFaceForm T htriangle hcard hvolume g p *
          monskyFaceForm T htriangle hcard hvolume g n < 0)
    (t : ↑T) :
    ∑ i : Fin 3, monskyIndicator
        (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) =
      monskyIndicator (p ∈ t.1) + monskyIndicator (n ∈ t.1) := by
  have h := monsky_form_parity
    (m := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume
      (.inl (t, i)) (monskyAtomMidpoint e))
    (p := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) p)
    (n := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) n)
    (occ := fun i : Fin 3 ↦ e ∈ monskyFaceAtomList T htriangle (.inl (t, i)))
    (monsky_triangle_atom_unique_zero T htriangle hcard hvolume f e hef t)
    (fun i ↦ hstable (.inl (t, i))) (fun i ↦ hflip (.inl (t, i)))
    (monsky_triangle_atom_occ_iff T htriangle hcard hvolume f e hef t)
  calc
    _ = monskyIndicator (∀ i : Fin 3,
          0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) p) +
        monskyIndicator (∀ i : Fin 3,
          0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) n) := h
    _ = _ := congrArg₂ (· + ·)
      (congrArg monskyIndicator
        (propext (monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t p))).symm
      (congrArg monskyIndicator
        (propext (monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t n))).symm

private lemma monsky_square_atom_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f)
    (p n : EuclideanSpace ℝ (Fin 2))
    (hstable : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g p ∧
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g n)
    (hflip : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
        monskyFaceForm T htriangle hcard hvolume g p *
          monskyFaceForm T htriangle hcard hvolume g n < 0) :
    ∑ i : Fin 4, monskyIndicator
        (e ∈ monskyFaceAtomList T htriangle (.inr i)) =
      monskyIndicator
          (p ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) +
        monskyIndicator
          (n ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) := by
  have h := monsky_form_parity
    (m := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume
      (.inr i) (monskyAtomMidpoint e))
    (p := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume (.inr i) p)
    (n := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume (.inr i) n)
    (occ := fun i : Fin 4 ↦ e ∈ monskyFaceAtomList T htriangle (.inr i))
    (monsky_square_atom_unique_zero T htriangle hcard hvolume f e hef)
    (fun i ↦ hstable (.inr i)) (fun i ↦ hflip (.inr i))
    (monsky_square_atom_occ_iff T htriangle hcard hvolume f e hef)
  calc
    _ = monskyIndicator (∀ i : Fin 4, 0 ≤ monskySquareSideForm i p) +
        monskyIndicator (∀ i : Fin 4, 0 ≤ monskySquareSideForm i n) := by
      simpa only [monskyFaceForm] using h
    _ = _ := congrArg₂ (· + ·)
      (congrArg monskyIndicator
        (propext (monsky_mem_unitSquare_iff_faceForms p))).symm
      (congrArg monskyIndicator
        (propext (monsky_mem_unitSquare_iff_faceForms n))).symm

private lemma monsky_tile_membership_unique
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (x : EuclideanSpace ℝ (Fin 2))
    (hface : ∀ (t : ↑T) (i : Fin 3),
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x ≠ 0)
    (t u : ↑T) (hxt : x ∈ t.1) (hxu : x ∈ u.1) : t = u := by
  apply Subtype.ext
  apply hdisjoint.elim t.2 u.2
  apply Set.not_disjoint_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · apply (monsky_mem_interior_tile_iff_faceForms
      T htriangle hcard hvolume t x).2
    intro i
    exact lt_of_le_of_ne
      ((monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t x).1 hxt i)
      (Ne.symm (hface t i))
  · apply (monsky_mem_interior_tile_iff_faceForms
      T htriangle hcard hvolume u x).2
    intro i
    exact lt_of_le_of_ne
      ((monsky_mem_tile_iff_faceForms T htriangle hcard hvolume u x).1 hxu i)
      (Ne.symm (hface u i))

private lemma monsky_sum_tile_indicator_eq_square
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (x : EuclideanSpace ℝ (Fin 2))
    (hface : ∀ (t : ↑T) (i : Fin 3),
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x ≠ 0) :
    ∑ t : ↑T, monskyIndicator (x ∈ t.1) =
      monskyIndicator
        (x ∈ {y : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ y.ofLp i ∧ y.ofLp i ≤ 1}) := by
  apply monsky_sum_indicator_eq_indicator_of_unique
  · constructor
    · intro hx
      have hxunion : x ∈ Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) :=
        hcover.symm ▸ hx
      obtain ⟨s, hsT, hxs⟩ := Set.mem_sUnion.mp hxunion
      exact ⟨⟨s, hsT⟩, hxs⟩
    · rintro ⟨t, hxt⟩
      rw [← hcover]
      exact Set.mem_sUnion_of_mem hxt t.2
  · intro t u hxt hxu
    exact monsky_tile_membership_unique
      T htriangle hcard hvolume hdisjoint x hface t u hxt hxu

private lemma monsky_atom_incidence_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) =
      ∑ i : Fin 4,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
  obtain ⟨p, n, hstable, hflip⟩ :=
    monsky_exists_atom_probes T htriangle hcard hvolume f e hef
  have hne := monsky_probe_faceForms_ne_zero
    T htriangle hcard hvolume e p n hstable hflip
  have hp := monsky_sum_tile_indicator_eq_square
    T htriangle hcard hvolume hcover hdisjoint p (fun t i ↦ (hne (.inl (t, i))).1)
  have hn := monsky_sum_tile_indicator_eq_square
    T htriangle hcard hvolume hcover hdisjoint n (fun t i ↦ (hne (.inl (t, i))).2)
  calc
    _ = ∑ t : ↑T, (monskyIndicator (p ∈ t.1) + monskyIndicator (n ∈ t.1)) :=
      Finset.sum_congr rfl fun t _ ↦
        monsky_triangle_atom_parity
          T htriangle hcard hvolume f e hef p n hstable hflip t
    _ = (∑ t : ↑T, monskyIndicator (p ∈ t.1)) +
        ∑ t : ↑T, monskyIndicator (n ∈ t.1) := Finset.sum_add_distrib
    _ = monskyIndicator
          (p ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) +
        monskyIndicator
          (n ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) := by
      rw [hp, hn]
    _ = _ := (monsky_square_atom_parity
      T htriangle hcard hvolume f e hef p n hstable hflip).symm

private noncomputable def monskyColor (V : ValuationSubring ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) : Fin 3 :=
  if 1 ≤ V.valuation (p.ofLp 0) ∧ V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0) then
    0
  else if 1 ≤ V.valuation (p.ofLp 1) then 1 else 2

private lemma monsky_edgeWeight_comm (i j : Fin 3) :
    monskyEdgeWeight i j = monskyEdgeWeight j i := by
  revert i j
  decide

private noncomputable def monskyAtomWeight (V : ValuationSubring ℝ) :
    Sym2 (EuclideanSpace ℝ (Fin 2)) → ZMod 2 :=
  Sym2.lift ⟨fun a b ↦ monskyEdgeWeight (monskyColor V a) (monskyColor V b), by
    intro a b
    exact monsky_edgeWeight_comm _ _⟩

@[simp] private lemma monsky_atomWeight_mk (V : ValuationSubring ℝ)
    (a b : EuclideanSpace ℝ (Fin 2)) :
    monskyAtomWeight V s(a, b) =
      monskyEdgeWeight (monskyColor V a) (monskyColor V b) := by
  rfl

private lemma monsky_facePointList_nodup
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFacePointList T htriangle f).Nodup := by
  rw [monskyFacePointList]
  exact (monsky_faceParamList_sorted T htriangle hcard hvolume f).nodup.map
    (AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f))

private lemma monsky_faceAtomList_nodup
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFaceAtomList T htriangle f).Nodup := by
  rw [monskyFaceAtomList]
  exact monsky_sym2_consecutivePairs_nodup _
    (monsky_facePointList_nodup T htriangle hcard hvolume f)

private lemma monsky_sum_atoms_weighted_faceIndicator (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) :
    ∑ e ∈ monskyAtoms T htriangle,
        monskyAtomWeight V e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle f) =
      ((monskyFaceAtomList T htriangle f).map (monskyAtomWeight V)).sum := by
  classical
  let s := (monskyFaceAtomList T htriangle f).toFinset
  have hsubset : s ⊆ monskyAtoms T htriangle := by
    intro e he
    simp only [s, List.mem_toFinset] at he
    simp only [monskyAtoms, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨f, by simpa using he⟩
  calc
    _ = ∑ e ∈ monskyAtoms T htriangle,
        if e ∈ s then monskyAtomWeight V e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hes : e ∈ s
      · have hesList : e ∈ monskyFaceAtomList T htriangle f := by
          simpa only [s, List.mem_toFinset] using hes
        simp [monskyIndicator, hes, hesList]
      · have henot : e ∉ monskyFaceAtomList T htriangle f := by
          simpa only [s, List.mem_toFinset] using hes
        simp [monskyIndicator, hes, henot]
    _ = ∑ e ∈ s, if e ∈ s then monskyAtomWeight V e else 0 := by
      symm
      apply Finset.sum_subset hsubset
      intro e he henot
      simp [henot]
    _ = ∑ e ∈ s, monskyAtomWeight V e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [he]
    _ = _ := List.sum_toFinset (monskyAtomWeight V)
      (monsky_faceAtomList_nodup T htriangle hcard hvolume f)

private lemma monsky_faceEndpointWeight_eq_sum_atoms (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) :
    monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle f))
        (monskyColor V (monskyFaceRight T htriangle f)) =
      ∑ e ∈ monskyAtoms T htriangle,
        monskyAtomWeight V e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle f) :=
  (monsky_sum_faceAtomWeight V T htriangle f).symm.trans
    (monsky_sum_atoms_weighted_faceIndicator
      V T htriangle hcard hvolume f).symm

private lemma monsky_triangle_boundary_eq_atom_sum (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
          (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) =
      ∑ e ∈ monskyAtoms T htriangle, monskyAtomWeight V e *
        ∑ t : ↑T, ∑ i : Fin 3,
          monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
  classical
  let A := monskyAtoms T htriangle
  let w := monskyAtomWeight V
  calc
    _ = ∑ t : ↑T, ∑ i : Fin 3, ∑ e ∈ A,
        w e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro i hi
      exact monsky_faceEndpointWeight_eq_sum_atoms
        V T htriangle hcard hvolume (.inl (t, i))
    _ = ∑ t : ↑T, ∑ e ∈ A, w e * ∑ i : Fin 3,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact monsky_sum_weighted_swap A w _
    _ = _ := by
      exact monsky_sum_weighted_swap A w _

private lemma monsky_square_boundary_eq_atom_sum (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    ∑ i : Fin 4,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inr i)))
          (monskyColor V (monskyFaceRight T htriangle (.inr i))) =
      ∑ e ∈ monskyAtoms T htriangle, monskyAtomWeight V e *
        ∑ i : Fin 4,
          monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
  classical
  let A := monskyAtoms T htriangle
  let w := monskyAtomWeight V
  calc
    _ = ∑ i : Fin 4, ∑ e ∈ A,
        w e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact monsky_faceEndpointWeight_eq_sum_atoms
        V T htriangle hcard hvolume (.inr i)
    _ = ∑ e ∈ A, w e * ∑ i : Fin 4,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) :=
      monsky_sum_weighted_swap A w _

private lemma monsky_boundary_weight_identity (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
          (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) =
      ∑ i : Fin 4,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inr i)))
          (monskyColor V (monskyFaceRight T htriangle (.inr i))) := by
  rw [monsky_triangle_boundary_eq_atom_sum V T htriangle hcard hvolume,
    monsky_square_boundary_eq_atom_sum V T htriangle hcard hvolume]
  apply Finset.sum_congr rfl
  intro e he
  apply congrArg (monskyAtomWeight V e * ·)
  obtain ⟨f, hef⟩ := monsky_atom_mem_exists_face T htriangle he
  exact monsky_atom_incidence_parity
    T htriangle hcard hvolume hcover hdisjoint f e hef

private lemma monsky_exists_rainbow_triangle (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior) :
    ∃ (t : ↑T) (a b c : EuclideanSpace ℝ (Fin 2)),
      t.1 = convexHull ℝ {a, b, c} ∧
        monskyColor V a = 0 ∧ monskyColor V b = 1 ∧ monskyColor V c = 2 := by
  have hsum : ∑ t : ↑T, ∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) = 1 :=
    (monsky_boundary_weight_identity
      V T htriangle hcard hvolume hcover hdisjoint).trans
      (monsky_square_boundary_weight_eq_one V T htriangle)
  have hsumne : (∑ t : ↑T, ∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i))))) ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨t, _, htne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have htone : (∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i))))) = 1 :=
    (monsky_zmod_two_eq_zero_or_one _).resolve_left htne
  let v := monskyVertices T htriangle t
  have hcycle :
      monskyEdgeWeight (monskyColor V (v 1)) (monskyColor V (v 2)) +
          monskyEdgeWeight (monskyColor V (v 2)) (monskyColor V (v 0)) +
        monskyEdgeWeight (monskyColor V (v 0)) (monskyColor V (v 1)) = 1 := by
    simpa [Fin.sum_univ_three, monskyFaceLeft, monskyFaceRight, v] using htone
  obtain ⟨h12, h20, h01⟩ :=
    (monskyEdgeWeight_triangle
      (monskyColor V (v 1)) (monskyColor V (v 2)) (monskyColor V (v 0))).1 hcycle
  let colorIndex : Fin 3 → Fin 3 := fun i ↦ monskyColor V (v i)
  have hinj : Function.Injective colorIndex := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [colorIndex]
  have hsurj : Function.Surjective colorIndex := Empty.Finite.surjective_of_injective hinj
  obtain ⟨i0, hi0⟩ := hsurj 0
  obtain ⟨i1, hi1⟩ := hsurj 1
  obtain ⟨i2, hi2⟩ := hsurj 2
  have hindices : ∀ i : Fin 3, i = i0 ∨ i = i1 ∨ i = i2 := by
    intro i
    have hc : colorIndex i = 0 ∨ colorIndex i = 1 ∨ colorIndex i = 2 := by
      generalize hci : colorIndex i = ci
      fin_cases ci <;> simp_all
    rcases hc with hc | hc | hc
    · exact Or.inl (hinj (hc.trans hi0.symm))
    · exact Or.inr (Or.inl (hinj (hc.trans hi1.symm)))
    · exact Or.inr (Or.inr (hinj (hc.trans hi2.symm)))
  have hrange : ({v i0, v i1, v i2} : Set (EuclideanSpace ℝ (Fin 2))) = Set.range v := by
    ext x
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨i0, rfl⟩
      · exact ⟨i1, rfl⟩
      · exact ⟨i2, rfl⟩
    · rintro ⟨i, rfl⟩
      rcases hindices i with rfl | rfl | rfl <;> simp
  refine ⟨t, v i0, v i1, v i2, ?_, hi0, hi1, hi2⟩
  rw [monsky_vertices_spec T htriangle t, ← hrange]

/-- Monsky's theorem (statement_id `monsky-s1`): a dissection of a square into
finitely many triangles of equal area (an equidissection) uses an even number
of triangles.

Source: Paul Monsky, "On Dividing A Square Into Triangles," *The American Mathematical
Monthly* 77(2) (1970), 161–164, DOI 10.1080/00029890.1970.11992441.

Proves `Wanted` entry `monsky_theorem`.

Proof: A 2-adic valuation on ℝ gives a three-colouring of the plane, and a Sperner-type parity
count supplies a rainbow triangle whose area valuation rules out an odd number of pieces.
-/
theorem monsky_theorem :
    ∀ (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
      (∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2), t = convexHull ℝ {a, b, c}) →
      Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
        {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} →
      (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior →
      (∃ A : ENNReal, ∀ t ∈ T, MeasureTheory.volume t = A) →
      Even T.card := by
  intro T htriangle hcover hdisjoint hcommon
  obtain ⟨A, hA⟩ := hcommon
  have hsum := monsky_sum_volume_eq_one T htriangle hcover hdisjoint
  obtain ⟨hcard, hvolume⟩ := monsky_common_volume_eq_card_inv T hsum A hA
  obtain ⟨V, hint, htwo⟩ := monsky_exists_valuation_int_le_one_two_lt_one
  obtain ⟨t, a, b, c, htabc, ha, hb, hc⟩ :=
    monsky_exists_rainbow_triangle
      V T htriangle hcard hvolume hcover hdisjoint
  by_contra heven
  exact monsky_odd_card_contradiction V hint htwo T
    (Nat.not_even_iff_odd.mp heven) hvolume t.2 a b c htabc ha hb hc

end MetaMathlibExt
