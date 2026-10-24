import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Dissections.Monsky
open MeasureTheory Set
open MetaMathlibExt


namespace MetaMathlibExt

/--
[monsky_volume_interior_convexHull_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_volume_interior_convexHull_triangle
  (a b c : EuclideanSpace ℝ (Fin 2)) :
  volume (interior (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))))) =
    volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) := by
  apply measure_eq_measure_of_null_sdiff interior_subset
  have hclosed : IsClosed
    (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) :=
    (by simp : Set.Finite
      ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))).isCompact_convexHull ℝ |>.isClosed
  rw [← hclosed.frontier_eq]
  exact (convex_convexHull ℝ _).addHaar_frontier volume

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_sum_volume_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_sum_volume_eq_one
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c})
  (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
    {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
  (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior) :
  ∑ t ∈ T, volume t = 1 := by
  let square : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}
  have hcover' : (⋃ t ∈ T, t) = square := by
    simpa only [sUnion_eq_biUnion, Finset.mem_coe, square] using hcover
  have hinterior :
    volume (⋃ t ∈ T, interior t) = ∑ t ∈ T, volume (interior t) :=
    measure_biUnion_finset hdisjoint fun _ _ ↦ isOpen_interior.measurableSet
  have hinterior_volume : ∀ t ∈ T, volume (interior t) = volume t := by
    intro t ht
    obtain ⟨a, b, c, rfl⟩ := htriangle t ht
    exact monsky_volume_interior_convexHull_triangle a b c
  have hsub : (⋃ t ∈ T, interior t) ⊆ square := by
    rw [← hcover']
    intro x hx
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨t, ht, hxt⟩ := hx
    exact ⟨t, ht, interior_subset hxt⟩
  apply le_antisymm
  · calc
    ∑ t ∈ T, volume t = volume (⋃ t ∈ T, interior t) := by
      rw [hinterior]
      exact (Finset.sum_congr rfl hinterior_volume).symm
    _ ≤ volume square := measure_mono hsub
    _ = 1 := MeasureTheory.volume_unitSquare
  · calc
    1 = volume square := MeasureTheory.volume_unitSquare.symm
    _ = volume (⋃ t ∈ T, t) := congrArg volume hcover'.symm
    _ ≤ ∑ t ∈ T, volume t := measure_biUnion_finset_le T id

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_common_volume_eq_card_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_common_volume_eq_card_inv
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (hsum : ∑ t ∈ T, volume t = 1) (A : ENNReal)
  (hA : ∀ t ∈ T, volume t = A) :
  T.card ≠ 0 ∧ ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ) := by
  have hsumA : (T.card : ENNReal) * A = 1 := by
    calc
      (T.card : ENNReal) * A = ∑ _t ∈ T, A := by simp
      _ = ∑ t ∈ T, volume t := Finset.sum_congr rfl fun t ht ↦ (hA t ht).symm
      _ = 1 := hsum
  have hcard : T.card ≠ 0 := by
    intro hzero
    simp [hzero] at hsumA
  have hAreal : A.toReal = 1 / (T.card : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast hcard)).2
    have hre := congrArg ENNReal.toReal hsumA
    simpa [mul_comm] using hre
  exact ⟨hcard, fun t ht ↦ by rw [hA t ht, hAreal]⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_abs_det_eq_two_div_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_abs_det_eq_two_div_card
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  {t : Set (EuclideanSpace ℝ (Fin 2))} (ht : t ∈ T)
  (a b c : EuclideanSpace ℝ (Fin 2))
  (htabc : t = convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) :
  |(a - c).ofLp 0 * (b - c).ofLp 1 -
    (a - c).ofLp 1 * (b - c).ofLp 0| = 2 / (T.card : ℝ) := by
  have hv := hvolume t ht
  rw [htabc] at hv
  have hv' :
    (volume (convexHull ℝ
      ({c, a, b} : Set (EuclideanSpace ℝ (Fin 2))))).toReal =
      1 / (T.card : ℝ) := by
    have hset : ({c, a, b} : Set (EuclideanSpace ℝ (Fin 2))) = {a, b, c} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    rwa [hset]
  rw [MeasureTheory.toReal_volume_convexHull_triangle] at hv'
  calc
    |(a - c).ofLp 0 * (b - c).ofLp 1 - (a - c).ofLp 1 * (b - c).ofLp 0| =
      2 * (|(a - c).ofLp 0 * (b - c).ofLp 1 -
        (a - c).ofLp 1 * (b - c).ofLp 0| / 2) := by ring
    _ = 2 * (1 / (T.card : ℝ)) := by rw [hv']
    _ = 2 / (T.card : ℝ) := by ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_triangleBasis_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_triangleBasis_apply
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  (t : ↑T) (i : Fin 3) :
  monskyTriangleBasis T htriangle hcard hvolume t i = monskyVertices T htriangle t i := by
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_faceForm_left_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_faceForm_left_right
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  (f : MonskyFace T) :
  monskyFaceForm T htriangle hcard hvolume f (monskyFaceLeft T htriangle f) = 0 ∧
    monskyFaceForm T htriangle hcard hvolume f (monskyFaceRight T htriangle f) = 0 := by
  obtain ⟨t, i⟩ | i := f
  · constructor <;> simp only [monskyFaceForm, monskyFaceLeft, monskyFaceRight]
    · rw [← monsky_triangleBasis_apply T htriangle hcard hvolume,
      (monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_ne]
      fin_omega
    · rw [← monsky_triangleBasis_apply T htriangle hcard hvolume,
      (monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_ne]
      fin_omega
  · fin_cases i <;> simp [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
    monskySquareSideForm, monskySquareCorner, monskyCoordinate]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_mem_unitSquare_iff_faceForms](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_mem_unitSquare_iff_faceForms
  (x : EuclideanSpace ℝ (Fin 2)) :
  x ∈ {y | ∀ i, 0 ≤ y.ofLp i ∧ y.ofLp i ≤ 1} ↔
    ∀ i : Fin 4, 0 ≤ monskySquareSideForm i x := by
  constructor
  · intro hx i
    fin_cases i <;> simp [monskySquareSideForm, monskyCoordinate] <;>
      have := hx 0 <;> have := hx 1 <;> linarith
  · intro h i
    fin_cases i
    · have hleft := h 3
      have hright := h 1
      simp [monskySquareSideForm, monskyCoordinate] at hleft hright
      simpa using And.intro hleft hright
    · have hbottom := h 0
      have htop := h 2
      simp [monskySquareSideForm, monskyCoordinate] at hbottom htop
      simpa using And.intro hbottom htop

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_faceForm_eq_zero_of_mem_line](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_faceForm_eq_zero_of_mem_line
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  (f : MonskyFace T) {x : EuclideanSpace ℝ (Fin 2)}
  (hx : x ∈ affineSpan ℝ
    ({monskyFaceLeft T htriangle f, monskyFaceRight T htriangle f} :
      Set (EuclideanSpace ℝ (Fin 2)))) :
  monskyFaceForm T htriangle hcard hvolume f x = 0 := by
  let g := monskyFaceForm T htriangle hcard hvolume f
  let z : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) 0
  have heq :
    ({monskyFaceLeft T htriangle f, monskyFaceRight T htriangle f} :
      Set (EuclideanSpace ℝ (Fin 2))).EqOn g z := by
    intro y hy
    obtain rfl | hy := hy
    · exact (monsky_faceForm_left_right T htriangle hcard hvolume f).1
    · rw [Set.mem_singleton_iff] at hy
      subst y
      exact (monsky_faceForm_left_right T htriangle hcard hvolume f).2
  exact AffineMap.eqOn_affineSpan heq hx

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_range_faceOpposite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_range_faceOpposite
  (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i : Fin 3) :
  Set.range ((⟨b, b.ind⟩ : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2).faceOpposite i).points =
    {b (i + 1), b (i + 2)} := by
  rw [Affine.Simplex.range_faceOpposite_points]
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨i + 1, by fin_cases i <;> decide, rfl⟩
    · exact ⟨i + 2, by fin_cases i <;> decide, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_mem_affineSpan_face_iff_coord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_mem_affineSpan_face_iff_coord_zero
  (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i : Fin 3)
  (x : EuclideanSpace ℝ (Fin 2)) :
  x ∈ affineSpan ℝ ({b (i + 1), b (i + 2)} : Set (EuclideanSpace ℝ (Fin 2))) ↔
    b.coord i x = 0 := by
  let s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨b, b.ind⟩
  rw [← monsky_range_faceOpposite b i]
  have h := Affine.Simplex.affineCombination_mem_affineSpan_faceOpposite_iff
    (s := s) (i := i) (w := fun j ↦ b.coord j x) (b.sum_coord_apply_eq_one x)
  rwa [b.affineCombination_coord_eq_self] at h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_mem_faceLine_iff_faceForm_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_mem_faceLine_iff_faceForm_eq_zero
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  (f : MonskyFace T) (x : EuclideanSpace ℝ (Fin 2)) :
  x ∈ monskyFaceLine T htriangle f ↔
    monskyFaceForm T htriangle hcard hvolume f x = 0 := by
  constructor
  · exact monsky_faceForm_eq_zero_of_mem_line T htriangle hcard hvolume f
  · intro hx
    obtain ⟨t, i⟩ | i := f
    · simpa only [monskyFaceLine, monskyFaceLeft, monskyFaceRight, monskyFaceForm,
      monsky_triangleBasis_apply] using
      ((monsky_mem_affineSpan_face_iff_coord_zero
        (monskyTriangleBasis T htriangle hcard hvolume t) i x).2 hx :
          x ∈ affineSpan ℝ
            ({monskyTriangleBasis T htriangle hcard hvolume t (i + 1),
              monskyTriangleBasis T htriangle hcard hvolume t (i + 2)} :
                Set (EuclideanSpace ℝ (Fin 2))))
    · rw [monskyFaceLine, mem_affineSpan_pair_iff_exists_lineMap_eq]
      fin_cases i
      · refine ⟨x.ofLp 0, ?_⟩
        ext j
        fin_cases j <;> norm_num [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
          monskySquareSideForm, monskySquareCorner, monskyCoordinate,
          AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
          smul_eq_mul] at hx ⊢
        all_goals linarith
      · refine ⟨x.ofLp 1, ?_⟩
        ext j
        fin_cases j <;> norm_num [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
          monskySquareSideForm, monskySquareCorner, monskyCoordinate,
          AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
          smul_eq_mul] at hx ⊢
        all_goals linarith
      · refine ⟨1 - x.ofLp 0, ?_⟩
        ext j
        fin_cases j <;> norm_num [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
          monskySquareSideForm, monskySquareCorner, monskyCoordinate,
          AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          PiLp.smul_apply, smul_eq_mul] at hx ⊢
        all_goals linarith
      · refine ⟨1 - x.ofLp 1, ?_⟩
        ext j
        fin_cases j <;> norm_num [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
          monskySquareSideForm, monskySquareCorner, monskyCoordinate,
          AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
          smul_eq_mul] at hx ⊢
        all_goals linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_intersectionPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_intersectionPoint_mem
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f g : MonskyFace T)
  (h : ((monskyFaceLine T htriangle f : Set (EuclideanSpace ℝ (Fin 2))) ∩
    monskyFaceLine T htriangle g).Nonempty) :
  monskyIntersectionPoint T htriangle f g ∈ monskyFaceLine T htriangle f ∧
    monskyIntersectionPoint T htriangle f g ∈ monskyFaceLine T htriangle g := by
  rw [monskyIntersectionPoint, dite_eq_left h]
  exact Classical.choose_spec h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_intersectionPoint_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_intersectionPoint_eq_of_mem
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f g : MonskyFace T)
  (hfg : monskyFaceLine T htriangle f ≠ monskyFaceLine T htriangle g)
  {x : EuclideanSpace ℝ (Fin 2)} (hxf : x ∈ monskyFaceLine T htriangle f)
  (hxg : x ∈ monskyFaceLine T htriangle g) :
  monskyIntersectionPoint T htriangle f g = x := by
  have hne : ((monskyFaceLine T htriangle f : Set (EuclideanSpace ℝ (Fin 2))) ∩
    monskyFaceLine T htriangle g).Nonempty := ⟨x, hxf, hxg⟩
  have hy := monsky_intersectionPoint_mem T htriangle f g hne
  by_contra hyx
  have hlinef : affineSpan ℝ
    ({monskyIntersectionPoint T htriangle f g, x} : Set (EuclideanSpace ℝ (Fin 2))) =
    monskyFaceLine T htriangle f :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hy.1 hxf hyx
  have hlineg : affineSpan ℝ
    ({monskyIntersectionPoint T htriangle f g, x} : Set (EuclideanSpace ℝ (Fin 2))) =
    monskyFaceLine T htriangle g :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hy.2 hxg hyx
  exact hfg (hlinef.symm.trans hlineg)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_faceLeft_mem_nodes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_faceLeft_mem_nodes
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
  monskyFaceLeft T htriangle f ∈ monskyNodes T htriangle := by
  classical
  simp [monskyNodes]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_faceRight_mem_nodes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_faceRight_mem_nodes
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
  monskyFaceRight T htriangle f ∈ monskyNodes T htriangle := by
  classical
  simp [monskyNodes]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_intersectionPoint_mem_nodes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_intersectionPoint_mem_nodes
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f g : MonskyFace T) :
  monskyIntersectionPoint T htriangle f g ∈ monskyNodes T htriangle := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨f, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_consecutivePairs_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_consecutivePairs_map {α β : Type*} (f : α → β) : ∀ l : List α,
  (l.map f).consecutivePairs = l.consecutivePairs.map (fun e ↦ (f e.1, f e.2)) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil =>
      rw [show [a].consecutivePairs = [] from rfl]
      rfl
    | cons b l =>
      simp only [List.map_cons]
      rw [show (f a :: f b :: l.map f).consecutivePairs =
        (f a, f b) :: (f b :: l.map f).consecutivePairs from rfl,
        show (a :: b :: l).consecutivePairs =
          (a, b) :: (b :: l).consecutivePairs from rfl]
      simp only [List.map_cons]
      congr

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_mem_faceAtomList_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_mem_faceAtomList_iff
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T)
  (e : Sym2 (EuclideanSpace ℝ (Fin 2))) :
  e ∈ monskyFaceAtomList T htriangle f ↔
    ∃ r q : ℝ, (r, q) ∈ (monskyFaceParamList T htriangle f).consecutivePairs ∧
      e = s(AffineMap.lineMap (monskyFaceLeft T htriangle f)
        (monskyFaceRight T htriangle f) r,
        AffineMap.lineMap (monskyFaceLeft T htriangle f)
          (monskyFaceRight T htriangle f) q) := by
  rw [monskyFaceAtomList, monskyFacePointList, monsky_consecutivePairs_map]
  simp only [List.mem_map]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q.1, q.2, hq, rfl⟩
  · rintro ⟨r, q, hrq, rfl⟩
    exact ⟨_, ⟨(r, q), hrq, rfl⟩, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_exists_valuation_int_le_one_two_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_exists_valuation_int_le_one_two_lt_one :
  ∃ V : ValuationSubring ℝ,
    (∀ z : ℤ, V.valuation (z : ℝ) ≤ 1) ∧ V.valuation 2 < 1 := by
  let A : Subring ℝ := (Int.castRingHom ℝ).range
  let e : ℤ ≃+* A := RingEquiv.ofBijective (Int.castRingHom ℝ).rangeRestrict
    ⟨fun x y h ↦ Int.cast_injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  let J : Ideal ℤ := Ideal.span {2}
  let I : Ideal A := J.comap e.symm
  have hJ : J ≠ ⊤ := by
    dsimp only [J]
    rw [ne_eq, Ideal.span_singleton_eq_top]
    norm_num [Int.isUnit_iff]
  have hI : I ≠ ⊤ := Ideal.comap_ne_top e.symm hJ
  obtain ⟨V, hAV, hnonunits⟩ :=
    Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨V, ?_, ?_⟩
  · intro z
    rw [V.valuation_le_one_iff]
    apply hAV
    exact ⟨z, rfl⟩
  · rw [← V.mem_nonunits_iff]
    let a2 : A := e 2
    have ha2 : a2 ∈ I := by
      change e.symm (e 2) ∈ J
      rw [e.symm_apply_apply]
      exact Ideal.subset_span (by simp)
    have hcoe : A.subtype a2 = (2 : ℝ) := by
      change ((2 : ℤ) : ℝ) = (2 : ℝ)
      norm_num
    exact hnonunits ⟨a2, ha2, hcoe⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_valuation_odd_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_valuation_odd_eq_one (V : ValuationSubring ℝ)
  (hint : ∀ z : ℤ, V.valuation (z : ℝ) ≤ 1) (htwo : V.valuation 2 < 1)
  {n : ℤ} (hn : Odd n) : V.valuation (n : ℝ) = 1 := by
  apply le_antisymm (hint n)
  by_contra hnot
  have hnlt : V.valuation (n : ℝ) < 1 := lt_of_not_ge hnot
  obtain ⟨m, hm⟩ := hn
  have hmle : V.valuation (m : ℝ) ≤ 1 := hint m
  have htwom : V.valuation ((2 : ℝ) * (m : ℝ)) < 1 := by
    rw [V.valuation.map_mul]
    calc
      V.valuation 2 * V.valuation (m : ℝ) ≤ V.valuation 2 * 1 := by
        simpa [mul_comm] using mul_le_mul_left hmle (V.valuation 2)
      _ = V.valuation 2 := mul_one _
      _ < 1 := htwo
  have hone : V.valuation (1 : ℝ) ≤
    max (V.valuation (n : ℝ)) (V.valuation (-((2 : ℝ) * (m : ℝ)))) := by
    have hadd := ValuationClass.map_add_le_max V.valuation
      (n : ℝ) (-((2 : ℝ) * (m : ℝ)))
    have hmR : (n : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
    have honeq : (n : ℝ) + -((2 : ℝ) * (m : ℝ)) = 1 := by
      rw [hmR]
      ring
    simpa only [honeq] using hadd
  rw [V.valuation.map_neg] at hone
  have hmax : max (V.valuation (n : ℝ))
    (V.valuation ((2 : ℝ) * (m : ℝ))) < 1 := max_lt hnlt htwom
  rw [V.valuation.map_one] at hone
  exact (not_lt_of_ge hone) hmax

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monskyEdgeWeight_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
most two colours. -/
private lemma monskyEdgeWeight_add (i j k : Fin 3) (h : i = j ∨ j = k ∨ i = k) :
  monskyEdgeWeight i k = monskyEdgeWeight i j + monskyEdgeWeight j k := by
  revert i j k
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monskyEdgeWeight_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
colours. -/
private lemma monskyEdgeWeight_triangle (i j k : Fin 3) :
  monskyEdgeWeight i j + monskyEdgeWeight j k + monskyEdgeWeight k i = 1 ↔
    i ≠ j ∧ j ≠ k ∧ k ≠ i := by
  revert i j k
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_pathWeight_eq_edgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_pathWeight_eq_edgeWeight (i j : Fin 3) : ∀ (l : List (Fin 3)),
  (∀ x ∈ l, x = i ∨ x = j) → (h : l ≠ []) →
    monskyPathWeight l = monskyEdgeWeight (l.head h) (l.getLast h) := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hall hne
    cases l with
    | nil =>
      simp only [monskyPathWeight, List.head_cons, List.getLast_singleton]
      simp [monskyEdgeWeight]
      omega
    | cons b l =>
      have htail : ∀ x ∈ b :: l, x = i ∨ x = j := by
        intro x hx
        exact hall x (by simp [hx])
      have htailne : b :: l ≠ [] := by simp
      have hih := ih htail htailne
      have ha := hall a (by simp)
      have hb := hall b (by simp)
      have hc := hall ((b :: l).getLast htailne)
        (List.mem_cons_of_mem a (List.getLast_mem htailne))
      have hdup : a = b ∨ b = (b :: l).getLast htailne ∨
        a = (b :: l).getLast htailne := by
        aesop
      rw [monskyPathWeight, hih]
      exact (monskyEdgeWeight_add a b ((b :: l).getLast htailne) hdup).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_mem_consecutivePairs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_mem_consecutivePairs_iff {α : Type*} {a b : α} : ∀ l : List α,
  (a, b) ∈ l.consecutivePairs ↔ ∃ pre post, l = pre ++ a :: b :: post := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      rw [show [x].consecutivePairs = [] from rfl]
      simp only [List.not_mem_nil, false_iff, not_exists]
      intro pre post h
      have hlen := congrArg List.length h
      simp at hlen
      omega
    | cons y l =>
      rw [show (x :: y :: l).consecutivePairs =
        (x, y) :: (y :: l).consecutivePairs from rfl]
      simp only [List.mem_cons, Prod.mk.injEq, ih]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨pre, post, h⟩)
        · exact ⟨[], l, rfl⟩
        · exact ⟨x :: pre, post, by simp [h]⟩
      · rintro ⟨pre, post, h⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at h
          exact Or.inl ⟨h.1.symm, h.2.1.symm⟩
        | cons z pre =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          exact Or.inr ⟨pre, post, h⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_not_between_of_mem_consecutivePairs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_not_between_of_mem_consecutivePairs {α : Type*} [LinearOrder α]
  {l : List α} (hs : l.SortedLT) {a b t : α}
  (hab : (a, b) ∈ l.consecutivePairs) (ht : t ∈ l) : ¬(a < t ∧ t < b) := by
  obtain ⟨pre, post, rfl⟩ := (monsky_mem_consecutivePairs_iff _).1 hab
  have hsappend := List.sortedLT_append.mp hs
  have htail : (a :: b :: post).SortedLT := hsappend.2.1
  have hpre : ∀ x ∈ pre, x < a := by
    intro x hx
    exact hsappend.2.2 x hx a (by simp)
  have hpost : ∀ x ∈ post, b < x := by
    intro x hx
    exact (List.sortedLT_cons.mp (List.sortedLT_cons.mp htail).2).1 x hx
  rintro ⟨hat, htb⟩
  obtain ht | ht := List.mem_append.mp ht
  · exact (not_lt_of_ge (hpre t ht).le) hat
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact lt_irrefl _ hat
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact lt_irrefl _ htb
      · exact (not_lt_of_ge (hpost t ht).le) htb

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_lt_of_mem_consecutivePairs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_lt_of_mem_consecutivePairs {α : Type*} [LinearOrder α]
  {l : List α} (hs : l.SortedLT) {a b : α}
  (hab : (a, b) ∈ l.consecutivePairs) : a < b := by
  obtain ⟨pre, post, rfl⟩ := (monsky_mem_consecutivePairs_iff _).1 hab
  have htail : (a :: b :: post).SortedLT := (List.sortedLT_append.mp hs).2.1
  exact (List.sortedLT_cons.mp htail).1 b (by simp)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_fst_mem_of_mem_consecutivePairs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_fst_mem_of_mem_consecutivePairs {α : Type*} {l : List α} {a b : α}
  (hab : (a, b) ∈ l.consecutivePairs) : a ∈ l := by
  obtain ⟨pre, post, rfl⟩ := (monsky_mem_consecutivePairs_iff _).1 hab
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_snd_mem_of_mem_consecutivePairs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_snd_mem_of_mem_consecutivePairs {α : Type*} {l : List α} {a b : α}
  (hab : (a, b) ∈ l.consecutivePairs) : b ∈ l := by
  obtain ⟨pre, post, rfl⟩ := (monsky_mem_consecutivePairs_iff _).1 hab
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_atomMidpoint_eq_lineMap_midpoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_atomMidpoint_eq_lineMap_midpoint
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T)
  (e : Sym2 (EuclideanSpace ℝ (Fin 2))) {r q : ℝ}
  (he : e = s(AffineMap.lineMap (monskyFaceLeft T htriangle f)
    (monskyFaceRight T htriangle f) r,
    AffineMap.lineMap (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f) q)) :
  monskyAtomMidpoint e =
    AffineMap.lineMap (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f) (midpoint ℝ r q) := by
  rw [he, monsky_atomMidpoint_mk]
  exact (AffineMap.lineMap _ _).map_midpoint r q |>.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_invFun_mem_faceInteriorParams](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_invFun_mem_faceInteriorParams
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T)
  {x : EuclideanSpace ℝ (Fin 2)} (hnode : x ∈ monskyNodes T htriangle)
  (hopen : x ∈ openSegment ℝ (monskyFaceLeft T htriangle f)
    (monskyFaceRight T htriangle f)) :
  Function.invFun (AffineMap.lineMap (monskyFaceLeft T htriangle f)
    (monskyFaceRight T htriangle f)) x ∈ monskyFaceInteriorParams T htriangle f := by
  classical
  rw [monskyFaceInteriorParams, Finset.mem_image]
  exact ⟨x, Finset.mem_filter.mpr ⟨hnode, hopen⟩, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_mem_consecutivePairs_of_sortedLT](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_mem_consecutivePairs_of_sortedLT {α : Type*} [LinearOrder α]
  {l : List α} (hs : l.SortedLT) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
  (hab : a < b) (hno : ∀ t ∈ l, ¬(a < t ∧ t < b)) :
  (a, b) ∈ l.consecutivePairs := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.mem_singleton] at ha hb
      subst x
      subst b
      exact (lt_irrefl _ hab).elim
    | cons y ys =>
      have hsorted := List.sortedLT_cons.mp hs
      have htailSorted : (y :: ys).SortedLT := hsorted.2
      rw [show (x :: y :: ys).consecutivePairs =
        (x, y) :: (y :: ys).consecutivePairs from rfl]
      by_cases hxa : x = a
      · subst x
        have hbTail : b ∈ y :: ys := by
          obtain hba | hbTail := List.mem_cons.mp hb
          · exact (hab.ne hba.symm).elim
          · exact hbTail
        obtain hby | hbys := List.mem_cons.mp hbTail
        · exact List.mem_cons.mpr (Or.inl (Prod.ext rfl hby))
        · have hay : a < y := hsorted.1 y (by simp)
          have hyb : y < b := (List.sortedLT_cons.mp htailSorted).1 b hbys
          exact (hno y (by simp) ⟨hay, hyb⟩).elim
      · apply List.mem_cons.mpr
        right
        have haTail : a ∈ y :: ys :=
          (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
        have hbTail : b ∈ y :: ys := by
          obtain hbx | hbTail := List.mem_cons.mp hb
          · subst x
            have hba : b < a := hsorted.1 a haTail
            exact (asymm hab hba).elim
          · exact hbTail
        exact ih htailSorted haTail hbTail
          (fun t ht ↦ hno t (List.mem_cons_of_mem x ht))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_scalar_segment_enclosure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_scalar_segment_enclosure {r q a b t : ℝ} (hrq : r < q)
  (ht : t ∈ Set.Ioo (0 : ℝ) 1)
  (hmid : midpoint ℝ r q = AffineMap.lineMap a b t)
  (ha : a ∉ Set.Ioo r q) (hb : b ∉ Set.Ioo r q) :
  (a ≤ r ∧ q ≤ b) ∨ (b ≤ r ∧ q ≤ a) := by
  have hru : r < midpoint ℝ r q := by
    simp only [midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    norm_num
    linarith
  have huq : midpoint ℝ r q < q := by
    simp only [midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    norm_num
    linarith
  obtain hab | hab | hab := lt_trichotomy a b
  · left
    have hau : a < midpoint ℝ r q := by
      rw [hmid]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      nlinarith [ht.1, ht.2]
    have hub : midpoint ℝ r q < b := by
      rw [hmid]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      nlinarith [ht.1, ht.2]
    constructor
    · by_contra h
      exact ha ⟨lt_of_not_ge h, hau.trans huq⟩
    · by_contra h
      exact hb ⟨hru.trans hub, lt_of_not_ge h⟩
  · subst b
    have hma : midpoint ℝ r q = a := by
      simpa [AffineMap.lineMap_apply] using hmid
    exact (ha ⟨hma ▸ hru, hma ▸ huq⟩).elim
  · right
    have hbu : b < midpoint ℝ r q := by
      rw [hmid]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      nlinarith [ht.1, ht.2]
    have hua : midpoint ℝ r q < a := by
      rw [hmid]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      nlinarith [ht.1, ht.2]
    constructor
    · by_contra h
      exact hb ⟨lt_of_not_ge h, hbu.trans huq⟩
    · by_contra h
      exact ha ⟨hru.trans hua, lt_of_not_ge h⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_faceForm_offPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_faceForm_offPoint_pos
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  (f : MonskyFace T) :
  0 < monskyFaceForm T htriangle hcard hvolume f
    (monskyFaceOffPoint T htriangle f) := by
  obtain ⟨t, i⟩ | i := f
  · simp only [monskyFaceForm, monskyFaceOffPoint,
    ← monsky_triangleBasis_apply T htriangle hcard hvolume]
    rw [(monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_eq]
    norm_num
  · fin_cases i <;> norm_num [monskyFaceForm, monskyFaceOffPoint,
    monskySquareSideForm, monskyCoordinate]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_faceForm_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_faceForm_continuous
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  (f : MonskyFace T) : Continuous (monskyFaceForm T htriangle hcard hvolume f) := by
  obtain ⟨t, i⟩ | i := f
  · exact continuous_barycentric_coord
    (monskyTriangleBasis T htriangle hcard hvolume t) i
  · fin_cases i
    all_goals norm_num [monskyFaceForm, monskySquareSideForm, monskyCoordinate]
    all_goals fun_prop

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_form_parity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_form_parity {ι : Type*} [Fintype ι]
  (m p n : ι → ℝ) (occ : ι → Prop)
  (hunique : ∀ i j, m i = 0 → m j = 0 → i = j)
  (hstable : ∀ i, m i ≠ 0 → 0 < m i * p i ∧ 0 < m i * n i)
  (hflip : ∀ i, m i = 0 → p i * n i < 0)
  (hocc : ∀ i, occ i ↔ m i = 0 ∧ ∀ j, j ≠ i → 0 < m j) :
  ∑ i, monskyIndicator (occ i) =
    monskyIndicator (∀ i, 0 ≤ p i) + monskyIndicator (∀ i, 0 ≤ n i) := by
  classical
  by_cases hz : ∃ k, m k = 0
  · obtain ⟨k, hk⟩ := hz
    have hzero : ∀ i, m i = 0 ↔ i = k := by
      intro i
      constructor
      · intro hi
        exact hunique i k hi hk
      · rintro rfl
        exact hk
    by_cases hall : ∀ j, j ≠ k → 0 < m j
    · have hocck : ∀ i, occ i ↔ i = k := by
      intro i
      rw [hocc, hzero]
      constructor
      · exact fun h ↦ h.1
      · rintro rfl
        exact ⟨rfl, hall⟩
      have hpother : ∀ i, i ≠ k → 0 < p i := by
        intro i hik
        have hm := hall i hik
        have hs := (hstable i (ne_of_gt hm)).1
        nlinarith
      have hnother : ∀ i, i ≠ k → 0 < n i := by
        intro i hik
        have hm := hall i hik
        have hs := (hstable i (ne_of_gt hm)).2
        nlinarith
      have hsum : ∑ i, monskyIndicator (occ i) = 1 := by
        simp_rw [hocck]
        simp only [monskyIndicator]
        simpa only [eq_comm] using
          (Fintype.sum_ite_eq k (fun _ ↦ (1 : ZMod 2)))
      rw [hsum]
      obtain hcase | hcase := (mul_neg_iff.mp (hflip k hk))
      · have hpall : ∀ i, 0 ≤ p i := by
        intro i
        by_cases hik : i = k
        · simpa [hik] using hcase.1.le
        · exact (hpother i hik).le
        have hnnot : ¬∀ i, 0 ≤ n i := by
          intro hn
          exact (not_lt_of_ge (hn k)) hcase.2
        simp [monskyIndicator, hpall, hnnot]
      · have hpnot : ¬∀ i, 0 ≤ p i := by
        intro hp
        exact (not_lt_of_ge (hp k)) hcase.1
        have hnall : ∀ i, 0 ≤ n i := by
          intro i
          by_cases hik : i = k
          · simpa [hik] using hcase.2.le
          · exact (hnother i hik).le
        simp [monskyIndicator, hpnot, hnall]
    · push Not at hall
      obtain ⟨j, hjk, hj⟩ := hall
      have hmj0 : m j ≠ 0 := by
        intro hmj
        exact hjk (hunique j k hmj hk)
      have hmjneg : m j < 0 := lt_of_le_of_ne hj hmj0
      have hpjneg : p j < 0 := by
        have hs := (hstable j hmj0).1
        nlinarith
      have hnjneg : n j < 0 := by
        have hs := (hstable j hmj0).2
        nlinarith
      have hoccfalse : ∀ i, ¬occ i := by
        intro i hi
        obtain ⟨hmi, hiother⟩ := (hocc i).1 hi
        have hik := hunique i k hmi hk
        subst i
        exact (not_lt_of_ge hj) (hiother j hjk)
      have hpnot : ¬∀ i, 0 ≤ p i := by
        intro hp
        exact (not_lt_of_ge (hp j)) hpjneg
      have hnnot : ¬∀ i, 0 ≤ n i := by
        intro hn
        exact (not_lt_of_ge (hn j)) hnjneg
      simp [monskyIndicator, hoccfalse, hpnot, hnnot]
  · push Not at hz
    have hoccfalse : ∀ i, ¬occ i := by
      intro i hi
      exact hz i ((hocc i).1 hi).1
    have hpiff : (∀ i, 0 ≤ p i) ↔ ∀ i, 0 ≤ m i := by
      constructor
      · intro hp i
        by_contra hmi
        have hmneg : m i < 0 := lt_of_not_ge hmi
        have hs := (hstable i (hz i)).1
        nlinarith [hp i]
      · intro hm i
        have hmpos : 0 < m i := lt_of_le_of_ne (hm i) (Ne.symm (hz i))
        have hs := (hstable i (hz i)).1
        nlinarith
    have hniff : (∀ i, 0 ≤ n i) ↔ ∀ i, 0 ≤ m i := by
      constructor
      · intro hn i
        by_contra hmi
        have hmneg : m i < 0 := lt_of_not_ge hmi
        have hs := (hstable i (hz i)).2
        nlinarith [hn i]
      · intro hm i
        have hmpos : 0 < m i := lt_of_le_of_ne (hm i) (Ne.symm (hz i))
        have hs := (hstable i (hz i)).2
        nlinarith
    rw [hpiff, hniff]
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    by_cases hm : ∀ i, 0 ≤ m i
    · simp [monskyIndicator, hoccfalse, hm, htwo]
    · simp [monskyIndicator, hoccfalse, hm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_mem_open_affineBasis_face_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_mem_open_affineBasis_face_iff
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (b : AffineBasis (Fin 3) ℝ V) (i : Fin 3) (x : V) :
  x ∈ openSegment ℝ (b (i + 1)) (b (i + 2)) ↔
    b.coord i x = 0 ∧ ∀ j, j ≠ i → 0 < b.coord j x := by
  rw [openSegment_eq_image_lineMap]
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · rw [(b.coord i).apply_lineMap]
      fin_cases i <;> norm_num [b.coord_apply, AffineMap.lineMap_apply]
    · intro j hji
      rw [(b.coord j).apply_lineMap]
      fin_cases i <;> fin_cases j
      all_goals norm_num [b.coord_apply, AffineMap.lineMap_apply] at hji
      all_goals norm_num [b.coord_apply, AffineMap.lineMap_apply]
      all_goals first | exact hr.1 | exact hr.2
  · rintro ⟨hi, hpos⟩
    have hsum := b.sum_coord_apply_eq_one x
    rw [Fin.sum_univ_three] at hsum
    fin_cases i
    · change b.coord 0 x = 0 at hi
      refine ⟨b.coord 2 x, ?_, ?_⟩
      · constructor
        · exact hpos 2 (by decide)
        · have := hpos 1 (by decide)
          linarith
      · apply b.ext_elem
        intro j
        rw [(b.coord j).apply_lineMap]
        fin_cases j <;> norm_num [b.coord_apply, AffineMap.lineMap_apply] <;> linarith
    · change b.coord 1 x = 0 at hi
      refine ⟨b.coord 0 x, ?_, ?_⟩
      · constructor
        · exact hpos 0 (by decide)
        · have := hpos 2 (by decide)
          linarith
      · apply b.ext_elem
        intro j
        rw [(b.coord j).apply_lineMap]
        fin_cases j <;> norm_num [b.coord_apply, AffineMap.lineMap_apply] <;> linarith
    · change b.coord 2 x = 0 at hi
      refine ⟨b.coord 1 x, ?_, ?_⟩
      · constructor
        · exact hpos 1 (by decide)
        · have := hpos 0 (by decide)
          linarith
      · apply b.ext_elem
        intro j
        rw [(b.coord j).apply_lineMap]
        fin_cases j <;> norm_num [b.coord_apply, AffineMap.lineMap_apply] <;> linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_triangle_faceLine_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_triangle_faceLine_injective
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) (t : ↑T) :
  Function.Injective fun i : Fin 3 ↦ monskyFaceLine T htriangle (.inl (t, i)) := by
  intro i j hij
  change monskyFaceLine T htriangle (.inl (t, i)) =
    monskyFaceLine T htriangle (.inl (t, j)) at hij
  by_contra hne
  have hvi : monskyFaceForm T htriangle hcard hvolume (.inl (t, i))
    (monskyVertices T htriangle t i) ≠ 0 := by
    simp only [monskyFaceForm, ← monsky_triangleBasis_apply T htriangle hcard hvolume]
    rw [(monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_eq]
    norm_num
  have hvj : monskyFaceForm T htriangle hcard hvolume (.inl (t, j))
    (monskyVertices T htriangle t i) = 0 := by
    simp only [monskyFaceForm, ← monsky_triangleBasis_apply T htriangle hcard hvolume]
    exact (monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_ne (Ne.symm hne)
  have hvjmem : monskyVertices T htriangle t i ∈
    monskyFaceLine T htriangle (.inl (t, j)) :=
    (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
      (.inl (t, j)) _).2 hvj
  rw [← hij] at hvjmem
  exact hvi ((monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inl (t, i)) _).1 hvjmem)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_square_faceLine_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_square_faceLine_injective
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
  Function.Injective fun i : Fin 4 ↦ monskyFaceLine T htriangle (.inr i) := by
  intro i j hij
  change monskyFaceLine T htriangle (.inr i) =
    monskyFaceLine T htriangle (.inr j) at hij
  by_contra hne
  let x := midpoint ℝ (monskyFaceLeft T htriangle (.inr i))
    (monskyFaceRight T htriangle (.inr i))
  have hxi : x ∈ monskyFaceLine T htriangle (.inr i) := by
    rw [monskyFaceLine]
    exact AffineMap.lineMap_mem_affineSpan_pair (⅟2 : ℝ) _ _
  have hxj : x ∈ monskyFaceLine T htriangle (.inr j) := by
    rwa [← hij]
  have hxjzero := (monsky_mem_faceLine_iff_faceForm_eq_zero
    T htriangle hcard hvolume (.inr j) x).1 hxj
  fin_cases i <;> fin_cases j
  all_goals norm_num at hne
  all_goals norm_num [x, monskyFaceForm, monskyFaceLeft, monskyFaceRight,
    monskySquareSideForm, monskySquareCorner, monskyCoordinate,
    midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
    smul_eq_mul] at hxjzero

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_mem_open_square_face_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_mem_open_square_face_iff
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (i : Fin 4) (x : EuclideanSpace ℝ (Fin 2)) :
  x ∈ openSegment ℝ (monskyFaceLeft T htriangle (.inr i))
    (monskyFaceRight T htriangle (.inr i)) ↔
    monskySquareSideForm i x = 0 ∧
      ∀ j, j ≠ i → 0 < monskySquareSideForm j x := by
  rw [openSegment_eq_image_lineMap]
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · fin_cases i <;> norm_num [monskyFaceLeft, monskyFaceRight,
      monskySquareSideForm, monskySquareCorner, monskyCoordinate,
      AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply, smul_eq_mul]
    · intro j hji
      fin_cases i <;> fin_cases j
      all_goals norm_num [monskyFaceLeft, monskyFaceRight, monskySquareSideForm,
        monskySquareCorner, monskyCoordinate, AffineMap.lineMap_apply,
        vsub_eq_sub, vadd_eq_add, PiLp.smul_apply, smul_eq_mul] at hji
      all_goals norm_num [monskyFaceLeft, monskyFaceRight, monskySquareSideForm,
        monskySquareCorner, monskyCoordinate, AffineMap.lineMap_apply,
        vsub_eq_sub, vadd_eq_add, PiLp.smul_apply, smul_eq_mul]
      all_goals first | exact hr.1 | exact hr.2
  · rintro ⟨hi, hpos⟩
    fin_cases i
    · refine ⟨x.ofLp 0, ?_, ?_⟩
      · have hxpos := hpos 3 (by decide)
        have hxlt := hpos 1 (by decide)
        change 0 < x.ofLp 0 at hxpos
        change 0 < 1 - x.ofLp 0 at hxlt
        exact ⟨hxpos, by linarith⟩
      · ext j
        fin_cases j <;> norm_num [monskyFaceLeft, monskyFaceRight,
          monskySquareCorner, AffineMap.lineMap_apply, vsub_eq_sub,
          vadd_eq_add, PiLp.smul_apply, smul_eq_mul, monskySquareSideForm,
          monskyCoordinate] at hi ⊢
        all_goals linarith
    · refine ⟨x.ofLp 1, ?_, ?_⟩
      · have hypos := hpos 0 (by decide)
        have hylt := hpos 2 (by decide)
        change 0 < x.ofLp 1 at hypos
        change 0 < 1 - x.ofLp 1 at hylt
        exact ⟨hypos, by linarith⟩
      · ext j
        fin_cases j <;> norm_num [monskyFaceLeft, monskyFaceRight,
          monskySquareCorner, AffineMap.lineMap_apply, vsub_eq_sub,
          vadd_eq_add, PiLp.smul_apply, smul_eq_mul, monskySquareSideForm,
          monskyCoordinate] at hi ⊢
        all_goals linarith
    · refine ⟨1 - x.ofLp 0, ?_, ?_⟩
      · have hxpos := hpos 3 (by decide)
        have hxlt := hpos 1 (by decide)
        change 0 < x.ofLp 0 at hxpos
        change 0 < 1 - x.ofLp 0 at hxlt
        exact ⟨by linarith, by linarith⟩
      · ext j
        fin_cases j <;> norm_num [monskyFaceLeft, monskyFaceRight,
          monskySquareCorner, AffineMap.lineMap_apply, vsub_eq_sub,
          vadd_eq_add, PiLp.smul_apply, smul_eq_mul, monskySquareSideForm,
          monskyCoordinate] at hi ⊢
        all_goals linarith
    · refine ⟨1 - x.ofLp 1, ?_, ?_⟩
      · have hypos := hpos 0 (by decide)
        have hylt := hpos 2 (by decide)
        change 0 < x.ofLp 1 at hypos
        change 0 < 1 - x.ofLp 1 at hylt
        exact ⟨by linarith, by linarith⟩
      · ext j
        fin_cases j <;> norm_num [monskyFaceLeft, monskyFaceRight,
          monskySquareCorner, AffineMap.lineMap_apply, vsub_eq_sub,
          vadd_eq_add, PiLp.smul_apply, smul_eq_mul, monskySquareSideForm,
          monskyCoordinate] at hi ⊢
        all_goals linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_sum_indicator_eq_indicator_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_sum_indicator_eq_indicator_of_unique
  {ι : Type*} [Fintype ι] (P : ι → Prop) (Q : Prop)
  (hexists : Q ↔ ∃ i, P i) (hunique : ∀ i j, P i → P j → i = j) :
  ∑ i, monskyIndicator (P i) = monskyIndicator Q := by
  classical
  by_cases hQ : Q
  · obtain ⟨k, hk⟩ := hexists.mp hQ
    have hP : ∀ i, P i ↔ i = k := by
      intro i
      exact ⟨fun hi ↦ hunique i k hi hk, fun hik ↦ hik ▸ hk⟩
    simp_rw [hP]
    simp [monskyIndicator, hQ]
  · have hP : ∀ i, ¬P i := by
    intro i hi
    exact hQ (hexists.mpr ⟨i, hi⟩)
    simp [monskyIndicator, hQ, hP]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_probe_faceForms_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_probe_faceForms_ne_zero
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
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
        monskyFaceForm T htriangle hcard hvolume g n < 0) (g : MonskyFace T) :
  monskyFaceForm T htriangle hcard hvolume g p ≠ 0 ∧
    monskyFaceForm T htriangle hcard hvolume g n ≠ 0 := by
  by_cases hm : monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0
  · have hprod := hflip g hm
    constructor <;> intro hzero <;> simp [hzero] at hprod
  · have hprod := hstable g hm
    constructor
    · intro hzero
      rw [hzero, mul_zero] at hprod
      exact (lt_irrefl 0) hprod.1
    · intro hzero
      rw [hzero, mul_zero] at hprod
      exact (lt_irrefl 0) hprod.2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_color_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_color_eq_zero_iff (V : ValuationSubring ℝ)
  (p : EuclideanSpace ℝ (Fin 2)) :
  monskyColor V p = 0 ↔
    1 ≤ V.valuation (p.ofLp 0) ∧
      V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0) := by
  by_cases h : 1 ≤ V.valuation (p.ofLp 0) ∧
    V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0)
  · simp [monskyColor, h]
  · by_cases hy : 1 ≤ V.valuation (p.ofLp 1)
    · simp [monskyColor, h, hy]
    · simp [monskyColor, h, hy]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_color_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_color_eq_one_iff (V : ValuationSubring ℝ)
  (p : EuclideanSpace ℝ (Fin 2)) :
  monskyColor V p = 1 ↔
    1 ≤ V.valuation (p.ofLp 1) ∧
      V.valuation (p.ofLp 0) < V.valuation (p.ofLp 1) := by
  by_cases h : 1 ≤ V.valuation (p.ofLp 0) ∧
    V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0)
  · have hnlt : ¬V.valuation (p.ofLp 0) < V.valuation (p.ofLp 1) :=
    not_lt_of_ge h.2
    simp [monskyColor, h, hnlt]
  · by_cases hy : 1 ≤ V.valuation (p.ofLp 1)
    · have hxlt : V.valuation (p.ofLp 0) < V.valuation (p.ofLp 1) := by
      by_contra hnlt
      have hyvx : V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0) :=
        le_of_not_gt hnlt
      exact h ⟨hy.trans hyvx, hyvx⟩
      simp [monskyColor, h, hy, hxlt]
    · simp [monskyColor, h, hy]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_color_eq_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_color_eq_two_iff (V : ValuationSubring ℝ)
  (p : EuclideanSpace ℝ (Fin 2)) :
  monskyColor V p = 2 ↔
    V.valuation (p.ofLp 0) < 1 ∧ V.valuation (p.ofLp 1) < 1 := by
  by_cases h : 1 ≤ V.valuation (p.ofLp 0) ∧
    V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0)
  · have hnx : ¬V.valuation (p.ofLp 0) < 1 := not_lt_of_ge h.1
    simp [monskyColor, h, hnx]
  · by_cases hy : 1 ≤ V.valuation (p.ofLp 1)
    · have hny : ¬V.valuation (p.ofLp 1) < 1 := not_lt_of_ge hy
      simp [monskyColor, h, hy, hny]
    · have hylt : V.valuation (p.ofLp 1) < 1 := lt_of_not_ge hy
      have hxlt : V.valuation (p.ofLp 0) < 1 := by
        by_contra hnx
        have hx : 1 ≤ V.valuation (p.ofLp 0) := le_of_not_gt hnx
        exact h ⟨hx, hylt.le.trans hx⟩
      simp [monskyColor, h, hy, hxlt, hylt]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_color_add_of_color_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_color_add_of_color_two (V : ValuationSubring ℝ)
  (p z : EuclideanSpace ℝ (Fin 2)) (hz : monskyColor V z = 2) :
  monskyColor V (p + z) = monskyColor V p := by
  obtain ⟨hz0, hz1⟩ := (monsky_color_eq_two_iff V z).1 hz
  generalize hc : monskyColor V p = c
  fin_cases c
  · obtain ⟨hp0, hp10⟩ := (monsky_color_eq_zero_iff V p).1 hc
    change monskyColor V (p + z) = 0
    have hx : V.valuation ((p + z).ofLp 0) = V.valuation (p.ofLp 0) := by
      simpa using V.valuation.map_add_eq_of_lt_left (hz0.trans_le hp0)
    rw [monsky_color_eq_zero_iff, hx]
    refine ⟨hp0, ?_⟩
    by_cases hp1 : 1 ≤ V.valuation (p.ofLp 1)
    · have hy : V.valuation ((p + z).ofLp 1) = V.valuation (p.ofLp 1) := by
      simpa using V.valuation.map_add_eq_of_lt_left (hz1.trans_le hp1)
      rwa [hy]
    · exact (V.valuation.map_add_lt (lt_of_not_ge hp1) hz1).le.trans hp0
  · obtain ⟨hp1, hp01⟩ := (monsky_color_eq_one_iff V p).1 hc
    change monskyColor V (p + z) = 1
    have hy : V.valuation ((p + z).ofLp 1) = V.valuation (p.ofLp 1) := by
      simpa using V.valuation.map_add_eq_of_lt_left (hz1.trans_le hp1)
    rw [monsky_color_eq_one_iff, hy]
    refine ⟨hp1, ?_⟩
    by_cases hp0 : 1 ≤ V.valuation (p.ofLp 0)
    · have hx : V.valuation ((p + z).ofLp 0) = V.valuation (p.ofLp 0) := by
      simpa using V.valuation.map_add_eq_of_lt_left (hz0.trans_le hp0)
      rwa [hx]
    · exact (V.valuation.map_add_lt (lt_of_not_ge hp0) hz0).trans_le hp1
  · obtain ⟨hp0, hp1⟩ := (monsky_color_eq_two_iff V p).1 hc
    change monskyColor V (p + z) = 2
    rw [monsky_color_eq_two_iff]
    exact ⟨by simpa using V.valuation.map_add_lt hp0 hz0,
      by simpa using V.valuation.map_add_lt hp1 hz1⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_det_ne_zero_of_colors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_det_ne_zero_of_colors (V : ValuationSubring ℝ)
  (a b c : EuclideanSpace ℝ (Fin 2)) (ha : monskyColor V a = 0)
  (hb : monskyColor V b = 1) (hc : monskyColor V c = 2) :
  (a - c).ofLp 0 * (b - c).ofLp 1 -
    (a - c).ofLp 1 * (b - c).ofLp 0 ≠ 0 := by
  obtain ⟨hc0, hc1⟩ := (monsky_color_eq_two_iff V c).1 hc
  have hnegc : monskyColor V (-c) = 2 := (monsky_color_eq_two_iff V (-c)).2 ⟨by
    simpa using (V.valuation.map_neg (c.ofLp 0)).trans_lt hc0, by
    simpa using (V.valuation.map_neg (c.ofLp 1)).trans_lt hc1⟩
  have ha' : monskyColor V (a - c) = 0 := by
    rw [sub_eq_add_neg, monsky_color_add_of_color_two V a (-c) hnegc, ha]
  have hb' : monskyColor V (b - c) = 1 := by
    rw [sub_eq_add_neg, monsky_color_add_of_color_two V b (-c) hnegc, hb]
  obtain ⟨ha0, ha10⟩ := (monsky_color_eq_zero_iff V (a - c)).1 ha'
  obtain ⟨hb1, hb01⟩ := (monsky_color_eq_one_iff V (b - c)).1 hb'
  intro hdet
  have hprod : (a - c).ofLp 0 * (b - c).ofLp 1 =
    (a - c).ofLp 1 * (b - c).ofLp 0 := sub_eq_zero.mp hdet
  have hval := congrArg V.valuation hprod
  rw [V.valuation.map_mul, V.valuation.map_mul] at hval
  have hlt : V.valuation ((a - c).ofLp 1) * V.valuation ((b - c).ofLp 0) <
    V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 1) := calc
    _ ≤ V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 0) :=
      mul_le_mul_left ha10 _
    _ < V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 1) :=
      mul_lt_mul_of_pos_left hb01 (zero_lt_one.trans_le ha0)
  exact hlt.ne hval.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_not_collinear_of_colors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_not_collinear_of_colors (V : ValuationSubring ℝ)
  (a b c : EuclideanSpace ℝ (Fin 2)) (ha : monskyColor V a = 0)
  (hb : monskyColor V b = 1) (hc : monskyColor V c = 2) :
  ¬Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hcollinear
  obtain ⟨p, v, hp⟩ :=
    (collinear_iff_exists_forall_eq_smul_vadd
      ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))).1 hcollinear
  obtain ⟨ra, hra⟩ := hp a (by simp)
  obtain ⟨rb, hrb⟩ := hp b (by simp)
  obtain ⟨rc, hrc⟩ := hp c (by simp)
  apply monsky_det_ne_zero_of_colors V a b c ha hb hc
  rw [hra, hrb, hrc]
  simp only [vadd_eq_add, add_sub_add_right_eq_sub, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_facePointList_mem_faceLine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_facePointList_mem_faceLine
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T)
  {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ monskyFacePointList T htriangle f) :
  x ∈ monskyFaceLine T htriangle f := by
  rw [monskyFacePointList, List.mem_map] at hx
  obtain ⟨r, _, rfl⟩ := hx
  rw [monskyFaceLine]
  exact AffineMap.lineMap_mem_affineSpan_pair r _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_facePointList_uses_two_colors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_facePointList_uses_two_colors (V : ValuationSubring ℝ)
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
  ∃ i j : Fin 3, ∀ x ∈ monskyFacePointList T htriangle f,
    monskyColor V x = i ∨ monskyColor V x = j := by
  classical
  by_cases hzero : ∃ x ∈ monskyFacePointList T htriangle f, monskyColor V x = 0
  · obtain ⟨a, haList, ha⟩ := hzero
    by_cases hone : ∃ x ∈ monskyFacePointList T htriangle f, monskyColor V x = 1
    · obtain ⟨b, hbList, hb⟩ := hone
      refine ⟨0, 1, ?_⟩
      intro x hxList
      have htwo : monskyColor V x ≠ 2 := by
        intro hx
        apply monsky_not_collinear_of_colors V a b x ha hb hx
        exact collinear_triple_of_mem_affineSpan_pair
          (monsky_facePointList_mem_faceLine T htriangle f haList)
          (monsky_facePointList_mem_faceLine T htriangle f hbList)
          (monsky_facePointList_mem_faceLine T htriangle f hxList)
      generalize hx : monskyColor V x = c
      fin_cases c <;> simp_all
    · refine ⟨0, 2, ?_⟩
      intro x hxList
      have hxone : monskyColor V x ≠ 1 := fun hx ↦ hone ⟨x, hxList, hx⟩
      generalize hx : monskyColor V x = c
      fin_cases c <;> simp_all
  · refine ⟨1, 2, ?_⟩
    intro x hxList
    have hxzero : monskyColor V x ≠ 0 := fun hx ↦ hzero ⟨x, hxList, hx⟩
    generalize hx : monskyColor V x = c
    fin_cases c <;> simp_all

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_pathWeight_eq_sum_consecutivePairs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_pathWeight_eq_sum_consecutivePairs : ∀ l : List (Fin 3),
  monskyPathWeight l =
    (l.consecutivePairs.map fun e ↦ monskyEdgeWeight e.1 e.2).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      rw [show (a :: b :: l).consecutivePairs =
        (a, b) :: (b :: l).consecutivePairs from rfl]
      simp only [List.map_cons, List.sum_cons, monskyPathWeight]
      rw [ih]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_facePointList_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_facePointList_ne_nil
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
  monskyFacePointList T htriangle f ≠ [] := by
  simp [monskyFacePointList, monskyFaceParamList]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_facePointList_head](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_facePointList_head
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
  (monskyFacePointList T htriangle f).head
    (monsky_facePointList_ne_nil T htriangle f) = monskyFaceLeft T htriangle f := by
  simp [monskyFacePointList, monskyFaceParamList, AffineMap.lineMap_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_facePointList_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_facePointList_getLast
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
  (monskyFacePointList T htriangle f).getLast
    (monsky_facePointList_ne_nil T htriangle f) = monskyFaceRight T htriangle f := by
  simp [monskyFacePointList, monskyFaceParamList, AffineMap.lineMap_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_sum_faceAtomWeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_sum_faceAtomWeight (V : ValuationSubring ℝ)
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
  ((monskyFaceAtomList T htriangle f).map (monskyAtomWeight V)).sum =
    monskyEdgeWeight
      (monskyColor V (monskyFaceLeft T htriangle f))
      (monskyColor V (monskyFaceRight T htriangle f)) := by
  let l := monskyFacePointList T htriangle f
  obtain ⟨i, j, hij⟩ := monsky_facePointList_uses_two_colors V T htriangle f
  have hall : ∀ c ∈ l.map (monskyColor V), c = i ∨ c = j := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact hij x hx
  have hne : l.map (monskyColor V) ≠ [] := by
    rw [Ne, List.map_eq_nil_iff]
    exact monsky_facePointList_ne_nil T htriangle f
  calc
    _ = (l.consecutivePairs.map fun e ↦
      monskyEdgeWeight (monskyColor V e.1) (monskyColor V e.2)).sum := by
      change ((l.consecutivePairs.map fun e ↦ s(e.1, e.2)).map
        (monskyAtomWeight V)).sum = _
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      obtain ⟨a, b⟩ := e
      rfl
    _ = monskyPathWeight (l.map (monskyColor V)) := by
      rw [monsky_pathWeight_eq_sum_consecutivePairs, monsky_consecutivePairs_map]
      apply congrArg List.sum
      rw [List.map_map]
      apply List.map_congr_left
      intro e he
      rfl
    _ = monskyEdgeWeight
      ((l.map (monskyColor V)).head hne) ((l.map (monskyColor V)).getLast hne) :=
      monsky_pathWeight_eq_edgeWeight i j _ hall hne
    _ = _ := by
      rw [List.head_map, List.getLast_map, monsky_facePointList_head,
        monsky_facePointList_getLast]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_sym2_consecutivePairs_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_sym2_consecutivePairs_nodup {α : Type*} : ∀ l : List α,
  l.Nodup → (l.consecutivePairs.map fun e ↦ s(e.1, e.2)).Nodup := by
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil =>
      rwa [show [a].consecutivePairs = [] from rfl]
    | cons b l =>
      rw [show (a :: b :: l).consecutivePairs =
        (a, b) :: (b :: l).consecutivePairs from rfl, List.map_cons,
        List.nodup_cons]
      refine ⟨?_, ih hl.tail⟩
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨⟨x, y⟩, hxy, heq⟩ := hmem
      have ha : a ∈ s(x, y) := by
        rw [heq]
        exact Sym2.mem_mk_left a b
      rw [Sym2.mem_iff] at ha
      have ha_not : a ∉ b :: l := (List.nodup_cons.mp hl).1
      obtain hax | hay := ha
      · exact ha_not (hax ▸ monsky_fst_mem_of_mem_consecutivePairs hxy)
      · exact ha_not (hay ▸ monsky_snd_mem_of_mem_consecutivePairs hxy)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_atom_mem_exists_face](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_atom_mem_exists_face
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c})
  {e : Sym2 (EuclideanSpace ℝ (Fin 2))} (he : e ∈ monskyAtoms T htriangle) :
  ∃ f : MonskyFace T, e ∈ monskyFaceAtomList T htriangle f := by
  rw [monskyAtoms, Finset.mem_biUnion] at he
  obtain ⟨f, _, hef⟩ := he
  exact ⟨f, List.mem_toFinset.mp hef⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_sum_weighted_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_sum_weighted_swap {α β : Type*} [Fintype β]
  (s : Finset α) (w : α → ZMod 2) (q : α → β → ZMod 2) :
  ∑ b : β, ∑ a ∈ s, w a * q a b =
    ∑ a ∈ s, w a * ∑ b : β, q a b := by
  classical
  calc
    _ = ∑ a ∈ s, ∑ b : β, w a * q a b := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_square_boundary_weight_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_square_boundary_weight_eq_one (V : ValuationSubring ℝ)
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
  (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
    t = convexHull ℝ {a, b, c}) :
  ∑ i : Fin 4,
    monskyEdgeWeight
      (monskyColor V (monskyFaceLeft T htriangle (.inr i)))
      (monskyColor V (monskyFaceRight T htriangle (.inr i))) = 1 := by
  have h0 : monskyColor V (monskySquareCorner 0) = 2 :=
    (monsky_color_eq_two_iff V _).2 (by
      norm_num [monskySquareCorner])
  have h1 : monskyColor V (monskySquareCorner 1) = 0 :=
    (monsky_color_eq_zero_iff V _).2 (by
      norm_num [monskySquareCorner])
  have h2 : monskyColor V (monskySquareCorner 2) = 0 :=
    (monsky_color_eq_zero_iff V _).2 (by
      norm_num [monskySquareCorner])
  have h3 : monskyColor V (monskySquareCorner 3) = 1 :=
    (monsky_color_eq_one_iff V _).2 (by
      norm_num [monskySquareCorner])
  rw [Fin.sum_univ_four]
  norm_num [monskyFaceLeft, monskyFaceRight, h0, h1, h2, h3, monskyEdgeWeight]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_zmod_two_eq_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val = 0 ∨ x.val = 1 := by
    have := x.val_lt
    omega
  obtain hx | hx := hx
  · left
    apply ZMod.val_injective
    simpa using hx
  · right
    apply ZMod.val_injective
    rwa [ZMod.val_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_one_le_valuation_det_of_colors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_one_le_valuation_det_of_colors (V : ValuationSubring ℝ)
  (a b c : EuclideanSpace ℝ (Fin 2)) (ha : monskyColor V a = 0)
  (hb : monskyColor V b = 1) (hc : monskyColor V c = 2) :
  1 ≤ V.valuation ((a - c).ofLp 0 * (b - c).ofLp 1 -
    (a - c).ofLp 1 * (b - c).ofLp 0) := by
  obtain ⟨hc0, hc1⟩ := (monsky_color_eq_two_iff V c).1 hc
  have hnegc : monskyColor V (-c) = 2 := (monsky_color_eq_two_iff V (-c)).2 ⟨by
    simpa using (V.valuation.map_neg (c.ofLp 0)).trans_lt hc0, by
    simpa using (V.valuation.map_neg (c.ofLp 1)).trans_lt hc1⟩
  have ha' : monskyColor V (a - c) = 0 := by
    rw [sub_eq_add_neg, monsky_color_add_of_color_two V a (-c) hnegc, ha]
  have hb' : monskyColor V (b - c) = 1 := by
    rw [sub_eq_add_neg, monsky_color_add_of_color_two V b (-c) hnegc, hb]
  obtain ⟨ha0, ha10⟩ := (monsky_color_eq_zero_iff V (a - c)).1 ha'
  obtain ⟨hb1, hb01⟩ := (monsky_color_eq_one_iff V (b - c)).1 hb'
  have hlt : V.valuation ((a - c).ofLp 1 * (b - c).ofLp 0) <
    V.valuation ((a - c).ofLp 0 * (b - c).ofLp 1) := by
    simp only [V.valuation.map_mul]
    calc
      _ ≤ V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 0) :=
        mul_le_mul_left ha10 _
      _ < V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 1) :=
        mul_lt_mul_of_pos_left hb01 (zero_lt_one.trans_le ha0)
  rw [V.valuation.map_sub_eq_of_lt_left hlt, V.valuation.map_mul]
  simpa only [one_mul] using mul_le_mul' ha0 hb1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monsky_odd_card_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_odd_card_contradiction (V : ValuationSubring ℝ)
  (hint : ∀ z : ℤ, V.valuation (z : ℝ) ≤ 1) (htwo : V.valuation 2 < 1)
  (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))) (hodd : Odd T.card)
  (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
  {t : Set (EuclideanSpace ℝ (Fin 2))} (ht : t ∈ T)
  (a b c : EuclideanSpace ℝ (Fin 2))
  (htabc : t = convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))))
  (ha : monskyColor V a = 0) (hb : monskyColor V b = 1)
  (hc : monskyColor V c = 2) : False := by
  let d : ℝ := (a - c).ofLp 0 * (b - c).ofLp 1 -
    (a - c).ofLp 1 * (b - c).ofLp 0
  have habs : |d| = 2 / (T.card : ℝ) :=
    monsky_abs_det_eq_two_div_card T hvolume ht a b c htabc
  have hoddInt : Odd (T.card : ℤ) := by exact_mod_cast hodd
  have hcardVal : V.valuation (T.card : ℝ) = 1 := by
    simpa using monsky_valuation_odd_eq_one V hint htwo hoddInt
  have habsVal : V.valuation |d| = V.valuation d := by
    obtain hd | hd := abs_choice d
    · rw [hd]
    · rw [hd, V.valuation.map_neg]
  have hdVal : V.valuation d = V.valuation 2 := calc
    V.valuation d = V.valuation |d| := habsVal.symm
    _ = V.valuation (2 / (T.card : ℝ)) := congrArg V.valuation habs
    _ = V.valuation 2 / V.valuation (T.card : ℝ) := V.valuation.map_div _ _
    _ = V.valuation 2 := by rw [hcardVal, div_one]
  have hone : 1 ≤ V.valuation d :=
    monsky_one_le_valuation_det_of_colors V a b c ha hb hc
  exact (not_lt_of_ge (hdVal ▸ hone)) htwo

end MetaMathlibExt

/--
[monsky_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Dissections/Monsky.lean)
-/
@[path]
private lemma monsky_theorem_eq
  :
-- imply
  ∀ (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
    (∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2), t = convexHull ℝ {a, b, c}) →
    Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
    {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} →
    (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior →
    (∃ A : ENNReal, ∀ t ∈ T, MeasureTheory.volume t = A) →
    Even T.card := by
-- proof
  apply MetaMathlibExt.monsky_theorem


-- created on 2026-10-20
-- updated on 2026-10-23
