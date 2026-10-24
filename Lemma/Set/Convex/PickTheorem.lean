import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Convex.PickTheorem
open Filter MeasureTheory
open scoped Pointwise
open MetaMathlibExt


namespace MetaMathlibExt

/--
[pick_lattice_preimage_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_lattice_preimage_finite {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
  Set.Finite (pickCast ⁻¹' K) := by
  have hcast : Tendsto pickCast Filter.cofinite (cocompact (Fin 2 → ℝ)) := by
    convert! Tendsto.pi_map_coprodᵢ fun _ ↦ Int.tendsto_coe_cofinite
    · rw [coprodᵢ_cofinite]
    · rw [coprodᵢ_cocompact]
  exact tendsto_cofinite_cocompact_iff.mp hcast K hK

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_affineBasis_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_affineBasis_apply (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
  (i : Fin 3) : pickAffineBasis u v h i = pickTrianglePoints u v h i :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_coord_eq_basisOf_repr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_coord_eq_basisOf_repr (a : AffineBasis (Fin 3) ℝ (Fin 2 → ℝ))
  (ha0 : a 0 = 0) (j : {i : Fin 3 // i ≠ 0}) (x : Fin 2 → ℝ) :
  a.coord j x = (a.basisOf 0).repr x j := by
  let f : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
    ((Finsupp.lapply j).comp (a.basisOf 0).repr.toLinearMap).toAffineMap
  have hfa : f = a.coord j := by
    apply AffineMap.ext_on a.tot
    rintro _ ⟨i, rfl⟩
    obtain rfl | hi := eq_or_ne i 0
    · calc
      f (a 0) = 0 := by simp [f, ha0]
      _ = a.coord (j : Fin 3) (a 0) := (a.coord_apply_ne j.property).symm
    · let q : {i : Fin 3 // i ≠ 0} := ⟨i, hi⟩
      change ((a.basisOf 0).repr (a i)) j = a.coord (j : Fin 3) (a i)
      have hb : a i = a.basisOf 0 q := by simp [q, ha0]
      conv_lhs => rw [hb, Module.Basis.repr_self]
      rw [a.coord_apply, Finsupp.single_apply]
      by_cases hq : q = j
      · have hji : (j : Fin 3) = i := congrArg Subtype.val hq.symm
        simp [hq, hji]
      · have hji : (j : Fin 3) ≠ i := by
        intro hij
        exact hq (Subtype.ext hij.symm)
        simp [hq, hji]
  rw [← hfa]
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_repr_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_repr_reflect (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
  (x : Fin 2 → ℝ) (i : Fin 2) :
  (pickBasis u v h).repr (pickReflect u v h x) i =
    1 - (pickBasis u v h).repr x i := by
  rw [pickReflect, map_sub, map_add, Module.Basis.repr_self, Module.Basis.repr_self]
  fin_cases i <;> simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_reflect_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_reflect_reflect (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
  (x : Fin 2 → ℝ) : pickReflect u v h (pickReflect u v h x) = x := by
  simp [pickReflect]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_mem_reflect_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_mem_reflect_image_iff (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
  (x : Fin 2 → ℝ) :
  x ∈ pickReflect u v h '' pickTriangle u v h ↔ pickReflect u v h x ∈ pickTriangle u v h := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨pickReflect u v h x, hx, pick_reflect_reflect u v h x⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_mem_diagonal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_mem_diagonal_iff (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
  (x : Fin 2 → ℝ) :
  x ∈ pickDiagonal u v h ↔
    (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 = 1 := by
  rw [pickDiagonal, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub,
    Module.Basis.sumCoords_self_apply, sub_eq_zero]
  classical
  simp [Fin.sum_univ_two]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_diagonal_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_diagonal_ne_top (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
  pickDiagonal u v h ≠ ⊤ := by
  intro htop
  have hz : (0 : Fin 2 → ℝ) ∈ pickDiagonal u v h := by rw [htop]; trivial
  rw [pick_mem_diagonal_iff] at hz
  simp at hz

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_triangle_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_triangle_isCompact (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
  IsCompact (pickTriangle u v h) :=
(Set.finite_range (pickAffineBasis u v h)).isCompact_convexHull ℝ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_triangle_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_triangle_measurableSet (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
  MeasurableSet (pickTriangle u v h) :=
  (pick_triangle_isCompact u v h).isClosed.measurableSet

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_measurePreserving_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_measurePreserving_neg :
  MeasurePreserving (fun x : Fin 2 → ℝ ↦ -x) volume volume := by
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_neg]
    norm_num
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := (-1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp [hdet])
  rw [hdet] at hmap
  norm_num at hmap
  refine ⟨measurable_neg, ?_⟩
  convert hmap using 1
  ext x i
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_measurePreserving_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_measurePreserving_reflect (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
  MeasurePreserving (pickReflect u v h) volume volume := by
  change MeasurePreserving
    ((fun x : Fin 2 → ℝ ↦ pickBasis u v h 0 + pickBasis u v h 1 + x) ∘ fun x ↦ -x)
      volume volume
  exact (measurePreserving_add_left volume (pickBasis u v h 0 + pickBasis u v h 1)).comp
    pick_measurePreserving_neg

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_reflect_image_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_reflect_image_eq_preimage (u v : Fin 2 → ℤ)
  (h : pickDet u v ≠ 0) :
  pickReflect u v h '' pickTriangle u v h = pickReflect u v h ⁻¹' pickTriangle u v h := by
  ext x
  exact pick_mem_reflect_image_iff u v h x

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_reflected_triangle_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_reflected_triangle_measurableSet (u v : Fin 2 → ℤ)
  (h : pickDet u v ≠ 0) : MeasurableSet (pickReflect u v h '' pickTriangle u v h) := by
  rw [pick_reflect_image_eq_preimage]
  exact (pick_triangle_measurableSet u v h).preimage
    (pick_measurePreserving_reflect u v h).measurable

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_volume_reflected_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_volume_reflected_triangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
  volume (pickReflect u v h '' pickTriangle u v h) = volume (pickTriangle u v h) := by
  rw [pick_reflect_image_eq_preimage]
  exact (pick_measurePreserving_reflect u v h).measure_preimage
    (pick_triangle_measurableSet u v h).nullMeasurableSet

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_intMap_basisFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_intMap_basisFun (u v : Fin 2 → ℤ) (i : Fin 2) :
  pickIntMap u v ((Pi.basisFun ℤ (Fin 2)) i) = ![u, v] i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [pickIntMap, pickIntMatrix, Matrix.toLin'_apply, Pi.basisFun_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_sublatticeBasis_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_sublatticeBasis_apply (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
  (i : Fin 2) : (pickSublatticeBasis u v h i : Fin 2 → ℤ) = ![u, v] i := by
  rw [pickSublatticeBasis, Module.Basis.map_apply]
  change pickIntMap u v ((Pi.basisFun ℤ (Fin 2)) i) = ![u, v] i
  rw [pick_intMap_basisFun]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_fundamentalLatticePoints_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_fundamentalLatticePoints_finite (u v : Fin 2 → ℤ)
  (h : pickDet u v ≠ 0) : (pickFundamentalLatticePoints u v h).Finite := by
  apply (pick_lattice_preimage_finite (pickBasis u v h).parallelepiped.isCompact).subset
  intro z hz
  exact ZSpan.fundamentalDomain_subset_parallelepiped (pickBasis u v h) hz

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_triangleLatticePoints_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_triangleLatticePoints_finite (u v : Fin 2 → ℤ)
  (h : pickDet u v ≠ 0) : (pickLatticePoints (pickTriangle u v h)).Finite :=
  pick_lattice_preimage_finite (pick_triangle_isCompact u v h)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_mem_fundamentalDomain_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_mem_fundamentalDomain_iff (u v : Fin 2 → ℤ)
  (h : pickDet u v ≠ 0) (x : Fin 2 → ℝ) :
  x ∈ ZSpan.fundamentalDomain (pickBasis u v h) ↔
    0 ≤ (pickBasis u v h).repr x 0 ∧ (pickBasis u v h).repr x 0 < 1 ∧
      0 ≤ (pickBasis u v h).repr x 1 ∧ (pickBasis u v h).repr x 1 < 1 := by
  rw [ZSpan.mem_fundamentalDomain]
  constructor
  · intro hx
    exact ⟨(hx 0).1, (hx 0).2, (hx 1).1, (hx 1).2⟩
  · rintro ⟨h00, h01, h10, h11⟩ i
    fin_cases i
    · exact ⟨h00, h01⟩
    · exact ⟨h10, h11⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_u_ne_v](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_u_ne_v (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) : u ≠ v := by
  intro huv
  apply h
  rw [huv]
  simp [pickDet, mul_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_intReflect_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_intReflect_involutive (u v z : Fin 2 → ℤ) :
  pickIntReflect u v (pickIntReflect u v z) = z := by
  simp [pickIntReflect]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_side_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_side_apply (a c x : Fin 2 → ℝ) :
  pickSide a c x =
    (c 0 - a 0) * (x 1 - a 1) - (c 1 - a 1) * (x 0 - a 0) := by
  simp [pickSide, pickNormal]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_normal_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_normal_ne_zero {a c : Fin 2 → ℝ} (hac : a ≠ c) :
  pickNormal a c ≠ 0 := by
  intro hzero
  have h0 := DFunLike.congr_fun hzero ![0, 1]
  have h1 := DFunLike.congr_fun hzero ![1, 0]
  simp [pickNormal] at h0 h1
  apply hac
  funext i
  fin_cases i
  · change a 0 = c 0
    linarith
  · change a 1 = c 1
    linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_side_eq_zero_iff_mem_line](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_side_eq_zero_iff_mem_line {a c : Fin 2 → ℝ} (hac : a ≠ c)
  (x : Fin 2 → ℝ) : pickSide a c x = 0 ↔ x ∈ line[ℝ, a, c] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · intro hx
    rw [pick_side_apply] at hx
    by_cases h0 : c 0 - a 0 ≠ 0
    · refine ⟨(x 0 - a 0) / (c 0 - a 0), ?_⟩
      ext i
      fin_cases i
      · rw [AffineMap.lineMap_apply_module']
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (x 0 - a 0) / (c 0 - a 0) * (c 0 - a 0) + a 0 = x 0
        field_simp [h0]
        ring
      · rw [AffineMap.lineMap_apply_module']
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (x 0 - a 0) / (c 0 - a 0) * (c 1 - a 1) + a 1 = x 1
        field_simp [h0]
        nlinarith
    · have h1 : c 1 - a 1 ≠ 0 := by
      intro h1
      apply hac
      funext i
      fin_cases i
      · change a 0 = c 0
        exact sub_eq_zero.mp (not_ne_iff.mp h0) |>.symm
      · change a 1 = c 1
        exact sub_eq_zero.mp h1 |>.symm
      have h0eq : c 0 - a 0 = 0 := not_ne_iff.mp h0
      refine ⟨(x 1 - a 1) / (c 1 - a 1), ?_⟩
      ext i
      fin_cases i
      · rw [AffineMap.lineMap_apply_module']
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (x 1 - a 1) / (c 1 - a 1) * (c 0 - a 0) + a 0 = x 0
        simp only [h0eq, zero_mul, zero_sub, neg_eq_zero] at hx
        have hx0 : x 0 - a 0 = 0 := (mul_eq_zero.mp hx).resolve_left h1
        rw [h0eq, mul_zero, zero_add]
        nlinarith
      · rw [AffineMap.lineMap_apply_module']
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (x 1 - a 1) / (c 1 - a 1) * (c 1 - a 1) + a 1 = x 1
        field_simp [h1]
        ring
  · rintro ⟨r, rfl⟩
    rw [pick_side_apply, AffineMap.lineMap_apply_module']
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_mem_halfPlus_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_mem_halfPlus_iff (a c x : Fin 2 → ℝ) :
  x ∈ pickHalfPlus a c ↔ 0 ≤ pickSide a c x := by
  simp [pickHalfPlus, pickSide]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_mem_halfMinus_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_mem_halfMinus_iff (a c x : Fin 2 → ℝ) :
  x ∈ pickHalfMinus a c ↔ pickSide a c x ≤ 0 := by
  simp [pickHalfMinus, pickSide]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_halfPlus_convex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_halfPlus_convex (a c : Fin 2 → ℝ) : Convex ℝ (pickHalfPlus a c) :=
convex_halfSpace_ge (pickNormal a c).toLinearMap.isLinear _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_halfPlus_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_halfPlus_isClosed (a c : Fin 2 → ℝ) : IsClosed (pickHalfPlus a c) :=
  isClosed_Ici.preimage (pickNormal a c).continuous

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_halfMinus_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_halfMinus_isClosed (a c : Fin 2 → ℝ) : IsClosed (pickHalfMinus a c) :=
  isClosed_Iic.preimage (pickNormal a c).continuous

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_interior_halfPlus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_interior_halfPlus {a c : Fin 2 → ℝ} (hac : a ≠ c) :
  interior (pickHalfPlus a c) = {x | pickNormal a c a < pickNormal a c x} := by
  rw [pickHalfPlus, ← (pickNormal a c).isOpenMap_of_ne_zero
    (pick_normal_ne_zero hac) |>.preimage_interior_eq_interior_preimage
      (pickNormal a c).continuous, interior_Ici]
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_interior_halfMinus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_interior_halfMinus {a c : Fin 2 → ℝ} (hac : a ≠ c) :
  interior (pickHalfMinus a c) = {x | pickNormal a c x < pickNormal a c a} := by
  rw [pickHalfMinus, ← (pickNormal a c).isOpenMap_of_ne_zero
    (pick_normal_ne_zero hac) |>.preimage_interior_eq_interior_preimage
      (pickNormal a c).continuous, interior_Iic]
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_half_inter_eq_line](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_half_inter_eq_line {a c : Fin 2 → ℝ} (hac : a ≠ c) :
  pickHalfPlus a c ∩ pickHalfMinus a c = (line[ℝ, a, c] : Set (Fin 2 → ℝ)) := by
  ext x
  rw [Set.mem_inter_iff, pick_mem_halfPlus_iff, pick_mem_halfMinus_iff]
  constructor
  · rintro ⟨hpos, hneg⟩
    exact (pick_side_eq_zero_iff_mem_line hac x).1 (le_antisymm hneg hpos)
  · intro hx
    have hz := (pick_side_eq_zero_iff_mem_line hac x).2 hx
    rw [hz]
    exact ⟨le_rfl, le_rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_line_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_line_ne_top {a c : Fin 2 → ℝ} (hac : a ≠ c) : line[ℝ, a, c] ≠ ⊤ := by
  intro htop
  have hall : ∀ x : Fin 2 → ℝ, pickSide a c x = 0 := by
    intro x
    apply (pick_side_eq_zero_iff_mem_line hac x).2
    rw [htop]
    trivial
  have ha : pickNormal a c a = 0 := by
    have := hall 0
    simp [pickSide] at this
    linarith
  apply pick_normal_ne_zero hac
  ext x
  have hx := hall x
  change pickNormal a c x = 0
  change pickNormal a c x - pickNormal a c a = 0 at hx
  rwa [ha, sub_zero] at hx

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_inter_line_eq_segment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_inter_line_eq_segment {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
  {a c : Fin 2 → ℝ} (hac : a ≠ c) (ha : a ∈ P.extremePoints ℝ)
  (hc : c ∈ P.extremePoints ℝ) :
  P ∩ (line[ℝ, a, c] : Set (Fin 2 → ℝ)) = segment ℝ a c := by
  ext x
  constructor
  · rintro ⟨hxP, hxline⟩
    have hcol : Collinear ℝ ({a, x, c} : Set (Fin 2 → ℝ)) := by
      have h := collinear_insert_of_mem_affineSpan_pair hxline
      have hset : ({x, a, c} : Set (Fin 2 → ℝ)) = {a, x, c} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [← hset]
    obtain haxc | hxca | hcax := hcol.wbtw_or_wbtw_or_wbtw
    · exact haxc.mem_segment
    · rcases (mem_extremePoints_iff_forall_segment.mp hc).2 x hxP a ha.1 hxca.mem_segment
      with hxc | hac'
      · rw [hxc]
        exact right_mem_segment ℝ a c
      · exact (hac hac').elim
    · rcases (mem_extremePoints_iff_forall_segment.mp ha).2 c hc.1 x hxP hcax.mem_segment
      with hca | hxa
      · exact (hac hca.symm).elim
      · rw [hxa]
        exact left_mem_segment ℝ a c
  · intro hx
    refine ⟨hP.segment_subset ha.1 hc.1 hx, ?_⟩
    rw [← affineSegment_eq_segment ℝ] at hx
    exact affineSegment_subset_affineSpan ℝ a c hx

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_map_eq_of_mem_openSegment_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_map_eq_of_mem_openSegment_of_eq (f : StrongDual ℝ (Fin 2 → ℝ))
  {p q x : Fin 2 → ℝ} {r : ℝ} (hx : x ∈ openSegment ℝ p q)
  (hp : f p = r) (hq : f q = r) : f x = r := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  rw [map_add, map_smul, map_smul, hp, hq]
  simp only [smul_eq_mul]
  rw [← add_mul, hst, one_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_endpoint_eq_of_openSegment_max](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_endpoint_eq_of_openSegment_max (f : StrongDual ℝ (Fin 2 → ℝ))
  {p q x : Fin 2 → ℝ} (hx : x ∈ openSegment ℝ p q)
  (hp : f p ≤ f x) (hq : f q ≤ f x) : f p = f x ∧ f q = f x := by
  obtain ⟨s, t, hs, ht, hst, hxeq⟩ := hx
  have hmap := congrArg f hxeq
  rw [map_add, map_smul, map_smul] at hmap
  simp only [smul_eq_mul] at hmap
  have hsum : s * f x + t * f x = f x := by
    rw [← add_mul, hst, one_mul]
  constructor
  · apply le_antisymm hp
    apply le_of_not_gt
    intro hlt
    have hslt : s * f p < s * f x := mul_lt_mul_of_pos_left hlt hs
    have htle : t * f q ≤ t * f x := mul_le_mul_of_nonneg_left hq ht.le
    have := add_lt_add_of_lt_of_le hslt htle
    rw [hmap, hsum] at this
    exact (lt_irrefl _ this)
  · apply le_antisymm hq
    apply le_of_not_gt
    intro hlt
    have hsle : s * f p ≤ s * f x := mul_le_mul_of_nonneg_left hp hs.le
    have htlt : t * f q < t * f x := mul_lt_mul_of_pos_left hlt ht
    have := add_lt_add_of_le_of_lt hsle htlt
    rw [hmap, hsum] at this
    exact (lt_irrefl _ this)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_continuousLinearMap_apply_coordinates](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_continuousLinearMap_apply_coordinates
  (f : StrongDual ℝ (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
  f x = x 0 * f ![1, 0] + x 1 * f ![0, 1] := by
  have hx : x = x 0 • ![1, 0] + x 1 • ![0, 1] := by
    funext i
    fin_cases i <;> simp
  calc
    f x = f (x 0 • ![1, 0] + x 1 • ![0, 1]) := congrArg f hx
    _ = x 0 * f ![1, 0] + x 1 * f ![0, 1] := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_openSegment_subset_interior](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_openSegment_subset_interior {P : Set (Fin 2 → ℝ)}
  (hP : Convex ℝ P) (hPint : (interior P).Nonempty) {a b c d y : Fin 2 → ℝ}
  (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P) (hac : a ≠ c)
  (hyac : y ∈ openSegment ℝ a c) (hybd : y ∈ openSegment ℝ b d)
  (hbline : b ∉ line[ℝ, a, c]) : openSegment ℝ a c ⊆ interior P := by
  intro x hx
  by_contra hxint
  obtain ⟨f, hfne, hmax⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hP hxint hPint
  obtain ⟨hfa, hfc⟩ :=
    pick_endpoint_eq_of_openSegment_max f hx (hmax a ha) (hmax c hc)
  have hfy : f y = f x := pick_map_eq_of_mem_openSegment_of_eq f hyac hfa hfc
  have hfb_le : f b ≤ f y := by rw [hfy]; exact hmax b hb
  have hfd_le : f d ≤ f y := by rw [hfy]; exact hmax d hd
  obtain ⟨hfb, -⟩ := pick_endpoint_eq_of_openSegment_max f hybd hfb_le hfd_le
  have hw : f (c - a) = 0 := by rw [map_sub, hfc, hfa, sub_self]
  have hq : f (b - a) = 0 := by rw [map_sub, hfb, hfy, hfa, sub_self]
  have hw' :
    (c 0 - a 0) * f ![1, 0] + (c 1 - a 1) * f ![0, 1] = 0 := by
    have hcoord := pick_continuousLinearMap_apply_coordinates f (c - a)
    rw [hw] at hcoord
    simpa only [Pi.sub_apply] using hcoord.symm
  have hq' :
    (b 0 - a 0) * f ![1, 0] + (b 1 - a 1) * f ![0, 1] = 0 := by
    have hcoord := pick_continuousLinearMap_apply_coordinates f (b - a)
    rw [hq] at hcoord
    simpa only [Pi.sub_apply] using hcoord.symm
  have hdet :
    (c 0 - a 0) * (b 1 - a 1) - (c 1 - a 1) * (b 0 - a 0) ≠ 0 := by
    rw [← pick_side_apply]
    exact fun hz ↦ hbline ((pick_side_eq_zero_iff_mem_line hac b).1 hz)
  have hf0prod :
    ((c 0 - a 0) * (b 1 - a 1) - (c 1 - a 1) * (b 0 - a 0)) *
      f ![1, 0] = 0 := by
    linear_combination (b 1 - a 1) * hw' - (c 1 - a 1) * hq'
  have hf1prod :
    ((c 0 - a 0) * (b 1 - a 1) - (c 1 - a 1) * (b 0 - a 0)) *
      f ![0, 1] = 0 := by
    linear_combination (c 0 - a 0) * hq' - (b 0 - a 0) * hw'
  have hf0 : f ![1, 0] = 0 := (mul_eq_zero.mp hf0prod).resolve_left hdet
  have hf1 : f ![0, 1] = 0 := (mul_eq_zero.mp hf1prod).resolve_left hdet
  apply hfne
  ext z
  rw [pick_continuousLinearMap_apply_coordinates, hf0, hf1]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_side_combo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_side_combo (a c p q : Fin 2 → ℝ) (s t : ℝ) (hst : s + t = 1) :
  pickSide a c (s • p + t • q) = s * pickSide a c p + t * pickSide a c q := by
  simp only [pickSide, map_add, map_smul, smul_eq_mul]
  linear_combination (pickNormal a c a) * hst

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_extreme_of_extreme_inter_halfPlus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_extreme_of_extreme_inter_halfPlus {P : Set (Fin 2 → ℝ)}
  (hP : Convex ℝ P) {a c x : Fin 2 → ℝ}
  (hx : x ∈ (P ∩ pickHalfPlus a c).extremePoints ℝ) (hsx : 0 < pickSide a c x) :
  x ∈ P.extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨hx.1.1, ?_⟩
  intro y hy z hz hxyz
  obtain ⟨s, t, hs, ht, hst, hxeq⟩ := hxyz
  let sx := pickSide a c x
  let sy := pickSide a c y
  let sz := pickSide a c z
  let A := |sy| + |sz| + sx
  let r := sx / (2 * A)
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith [abs_nonneg sy, abs_nonneg sz]
  have hr : 0 < r := div_pos hsx (by positivity)
  have hr1 : r < 1 := by
    apply (div_lt_one (by positivity)).2
    dsimp only [A]
    nlinarith [abs_nonneg sy, abs_nonneg sz]
  have hrA : r * A = sx / 2 := by
    dsimp only [r]
    field_simp [ne_of_gt hA]
  have hry : r * (sx + |sy|) ≤ sx / 2 := by
    calc
      r * (sx + |sy|) ≤ r * A := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        dsimp only [A]
        linarith [abs_nonneg sz]
      _ = sx / 2 := hrA
  have hrz : r * (sx + |sz|) ≤ sx / 2 := by
    calc
      r * (sx + |sz|) ≤ r * A := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        dsimp only [A]
        linarith [abs_nonneg sy]
      _ = sx / 2 := hrA
  let y' := (1 - r) • x + r • y
  let z' := (1 - r) • x + r • z
  have hy'side : 0 < pickSide a c y' := by
    rw [show pickSide a c y' = (1 - r) * sx + r * sy by
      exact pick_side_combo a c x y (1 - r) r (by ring)]
    have hsy : -|sy| ≤ sy := neg_abs_le sy
    have hrsy : -(r * |sy|) ≤ r * sy := by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left hsy hr.le
    nlinarith
  have hz'side : 0 < pickSide a c z' := by
    rw [show pickSide a c z' = (1 - r) * sx + r * sz by
      exact pick_side_combo a c x z (1 - r) r (by ring)]
    have hsz : -|sz| ≤ sz := neg_abs_le sz
    have hrsz : -(r * |sz|) ≤ r * sz := by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left hsz hr.le
    nlinarith
  have hy'P : y' ∈ P := hP hx.1.1 hy (by linarith) hr.le (by ring)
  have hz'P : z' ∈ P := hP hx.1.1 hz (by linarith) hr.le (by ring)
  have hy' : y' ∈ P ∩ pickHalfPlus a c :=
    ⟨hy'P, (pick_mem_halfPlus_iff a c y').2 hy'side.le⟩
  have hz' : z' ∈ P ∩ pickHalfPlus a c :=
    ⟨hz'P, (pick_mem_halfPlus_iff a c z').2 hz'side.le⟩
  have hbetween : x ∈ openSegment ℝ y' z' := by
    refine ⟨s, t, hs, ht, hst, ?_⟩
    dsimp only [y', z']
    calc
      s • ((1 - r) • x + r • y) + t • ((1 - r) • x + r • z) =
        (s * (1 - r) + t * (1 - r)) • x + r • (s • y + t • z) := by module
      _ = (1 - r) • x + r • (s • y + t • z) := by rw [← add_mul, hst, one_mul]
      _ = (1 - r) • x + r • x := by rw [hxeq]
      _ = x := by module
  have hy'x : y' = x := hx.2 hy' hz' hbetween
  have hz'x : z' = x := hx.2 hz' hy' (by rwa [openSegment_symm])
  constructor
  · funext i
    have hi := congrFun hy'x i
    dsimp only [y'] at hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    nlinarith
  · funext i
    have hi := congrFun hz'x i
    dsimp only [z'] at hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    nlinarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_side_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_side_swap (a c x : Fin 2 → ℝ) :
  pickSide c a x = -pickSide a c x := by
  rw [pick_side_apply, pick_side_apply]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_halfMinus_eq_halfPlus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_halfMinus_eq_halfPlus (a c : Fin 2 → ℝ) :
  pickHalfMinus a c = pickHalfPlus c a := by
  ext x
  rw [pick_mem_halfMinus_iff, pick_mem_halfPlus_iff, pick_side_swap]
  constructor <;> intro h <;> linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_convexHull_inter_halfPlus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_convexHull_inter_halfPlus {S : Set (Fin 2 → ℝ)} (hS : S.Finite)
  {a c : Fin 2 → ℝ} (hac : a ≠ c)
  (ha : a ∈ (convexHull ℝ S).extremePoints ℝ)
  (hc : c ∈ (convexHull ℝ S).extremePoints ℝ) :
  convexHull ℝ (S ∩ pickHalfPlus a c) = convexHull ℝ S ∩ pickHalfPlus a c := by
  let P := convexHull ℝ S
  let K := P ∩ pickHalfPlus a c
  have hP : Convex ℝ P := convex_convexHull ℝ S
  have hK : Convex ℝ K := hP.inter (pick_halfPlus_convex a c)
  have hPcomp : IsCompact P := hS.isCompact_convexHull ℝ
  have hKcomp : IsCompact K := hPcomp.inter_right (pick_halfPlus_isClosed a c)
  have haS : a ∈ S := extremePoints_convexHull_subset ha
  have hcS : c ∈ S := extremePoints_convexHull_subset hc
  have haK : a ∈ K := ⟨ha.1, (pick_mem_halfPlus_iff a c a).2 (by simp [pickSide])⟩
  have hcK : c ∈ K := ⟨hc.1, (pick_mem_halfPlus_iff a c c).2 (by
    rw [pick_side_apply]
    ring_nf
    exact le_rfl)⟩
  have hext : K.extremePoints ℝ ⊆ S ∩ pickHalfPlus a c := by
    intro x hx
    have hxside := (pick_mem_halfPlus_iff a c x).1 hx.1.2
    refine ⟨?_, hx.1.2⟩
    obtain hxzero | hxpos := hxside.eq_or_lt
    · have hxline : x ∈ line[ℝ, a, c] :=
      (pick_side_eq_zero_iff_mem_line hac x).1 hxzero.symm
      have hxseg : x ∈ segment ℝ a c := by
        rw [← pick_inter_line_eq_segment hP hac ha hc]
        exact ⟨hx.1.1, hxline⟩
      obtain hax | hcx := (mem_extremePoints_iff_forall_segment.mp hx).2 a haK c hcK hxseg
      · simpa [hax] using haS
      · simpa [hcx] using hcS
    · exact extremePoints_convexHull_subset
      (pick_extreme_of_extreme_inter_halfPlus hP hx hxpos)
  apply Set.Subset.antisymm
  · exact convexHull_min (Set.inter_subset_inter_left _ (subset_convexHull ℝ S)) hK
  · change K ⊆ convexHull ℝ (S ∩ pickHalfPlus a c)
    rw [← closure_convexHull_extremePoints hKcomp hK]
    apply closure_minimal (convexHull_mono hext)
    exact (hS.inter_of_left (pickHalfPlus a c)).isCompact_convexHull ℝ |>.isClosed

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_convexHull_inter_halfMinus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_convexHull_inter_halfMinus {S : Set (Fin 2 → ℝ)} (hS : S.Finite)
  {a c : Fin 2 → ℝ} (hac : a ≠ c)
  (ha : a ∈ (convexHull ℝ S).extremePoints ℝ)
  (hc : c ∈ (convexHull ℝ S).extremePoints ℝ) :
  convexHull ℝ (S ∩ pickHalfMinus a c) = convexHull ℝ S ∩ pickHalfMinus a c := by
  rw [pick_halfMinus_eq_halfPlus]
  exact pick_convexHull_inter_halfPlus hS hac.symm hc ha

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_side_mul_side_neg_of_cross](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_side_mul_side_neg_of_cross {a b c d y : Fin 2 → ℝ}
  (hac : a ≠ c) (hyac : y ∈ openSegment ℝ a c) (hybd : y ∈ openSegment ℝ b d)
  (hbline : b ∉ line[ℝ, a, c]) : pickSide a c b * pickSide a c d < 0 := by
  have hyline : y ∈ line[ℝ, a, c] := by
    apply affineSegment_subset_affineSpan ℝ a c
    rw [affineSegment_eq_segment]
    exact openSegment_subset_segment ℝ a c hyac
  have hyzero : pickSide a c y = 0 := (pick_side_eq_zero_iff_mem_line hac y).2 hyline
  obtain ⟨s, t, hs, ht, hst, hyeq⟩ := hybd
  have hsum : s * pickSide a c b + t * pickSide a c d = 0 := by
    have h := congrArg (pickSide a c) hyeq
    rwa [pick_side_combo a c b d s t hst, hyzero] at h
  have hbzero : pickSide a c b ≠ 0 := fun hbzero ↦
    hbline ((pick_side_eq_zero_iff_mem_line hac b).1 hbzero)
  obtain hbneg | hbpos := lt_or_gt_of_ne hbzero
  · have hsneg : s * pickSide a c b < 0 := mul_neg_of_pos_of_neg hs hbneg
    have htdpos : 0 < t * pickSide a c d := by linarith
    have hdpos : 0 < pickSide a c d := by
      obtain ⟨-, hdpos⟩ | ⟨htneg, -⟩ := (mul_pos_iff.mp htdpos)
      · exact hdpos
      · exact (htneg.not_gt ht).elim
    exact mul_neg_of_neg_of_pos hbneg hdpos
  · have hspos : 0 < s * pickSide a c b := mul_pos hs hbpos
    have htdneg : t * pickSide a c d < 0 := by linarith
    have hdneg : pickSide a c d < 0 := by
      obtain ⟨-, hdneg⟩ | ⟨htneg, -⟩ := (mul_neg_iff.mp htdneg)
      · exact hdneg
      · exact (htneg.not_gt ht).elim
    exact mul_neg_of_pos_of_neg hbpos hdneg

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_interior_inter_halfPlus_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_interior_inter_halfPlus_nonempty {P : Set (Fin 2 → ℝ)}
  (hP : Convex ℝ P) (hPclosed : IsClosed P) (hPint : (interior P).Nonempty)
  {a c x : Fin 2 → ℝ} (hac : a ≠ c) (hxP : x ∈ P) (hxside : 0 < pickSide a c x) :
  (interior (P ∩ pickHalfPlus a c)).Nonempty := by
  let U : Set (Fin 2 → ℝ) := {z | pickNormal a c a < pickNormal a c z}
  have hUopen : IsOpen U := isOpen_lt continuous_const (pickNormal a c).continuous
  have hxU : x ∈ U := by
    change pickNormal a c a < pickNormal a c x
    dsimp only [pickSide] at hxside
    linarith
  have hxcl : x ∈ closure (interior P) := by
    rwa [hP.closure_interior_eq_closure_of_nonempty_interior hPint, hPclosed.closure_eq]
  obtain ⟨z, hzU, hzP⟩ := (mem_closure_iff.mp hxcl) U hUopen hxU
  refine ⟨z, ?_⟩
  rw [interior_inter, pick_interior_halfPlus hac]
  exact ⟨hzP, hzU⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_interior_inter_halfMinus_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_interior_inter_halfMinus_nonempty {P : Set (Fin 2 → ℝ)}
  (hP : Convex ℝ P) (hPclosed : IsClosed P) (hPint : (interior P).Nonempty)
  {a c x : Fin 2 → ℝ} (hac : a ≠ c) (hxP : x ∈ P) (hxside : pickSide a c x < 0) :
  (interior (P ∩ pickHalfMinus a c)).Nonempty := by
  rw [pick_halfMinus_eq_halfPlus]
  apply pick_interior_inter_halfPlus_nonempty hP hPclosed hPint hac.symm hxP
  rw [pick_side_swap]
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_interior_cut](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_interior_cut {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
  (hPint : (interior P).Nonempty) {a b c d y : Fin 2 → ℝ}
  (ha : a ∈ P.extremePoints ℝ) (hb : b ∈ P) (hc : c ∈ P.extremePoints ℝ)
  (hd : d ∈ P) (hac : a ≠ c) (hyac : y ∈ openSegment ℝ a c)
  (hybd : y ∈ openSegment ℝ b d) (hbline : b ∉ line[ℝ, a, c]) :
  interior P =
    (interior (P ∩ pickHalfPlus a c) ∪ interior (P ∩ pickHalfMinus a c)) ∪
      openSegment ℝ a c := by
  have hopen : openSegment ℝ a c ⊆ interior P :=
    pick_openSegment_subset_interior hP hPint ha.1 hb hc.1 hd hac hyac hybd hbline
  ext x
  constructor
  · intro hx
    obtain hneg | heq | hpos := lt_trichotomy (pickNormal a c x) (pickNormal a c a)
    · left
      right
      rw [interior_inter, pick_interior_halfMinus hac]
      exact ⟨hx, hneg⟩
    · right
      have hxline : x ∈ line[ℝ, a, c] := by
        apply (pick_side_eq_zero_iff_mem_line hac x).1
        dsimp only [pickSide]
        linarith
      have hxseg : x ∈ segment ℝ a c := by
        rw [← pick_inter_line_eq_segment hP hac ha hc]
        exact ⟨interior_subset hx, hxline⟩
      rw [← insert_endpoints_openSegment ℝ] at hxseg
      obtain hxa | hxc | hxopen := hxseg
      · exact (Set.disjoint_left.mp (disjoint_interior_extremePoints P) hx
        (hxa ▸ ha)).elim
      · exact (Set.disjoint_left.mp (disjoint_interior_extremePoints P) hx
        (hxc ▸ hc)).elim
      · exact hxopen
    · left
      left
      rw [interior_inter, pick_interior_halfPlus hac]
      exact ⟨hx, hpos⟩
  · rintro ((hx | hx) | hx)
    · exact interior_mono Set.inter_subset_left hx
    · exact interior_mono Set.inter_subset_left hx
    · exact hopen hx

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_lattice_ncard_eq_interior_add_frontier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_lattice_ncard_eq_interior_add_frontier {K : Set (Fin 2 → ℝ)}
  (hK : IsCompact K) :
  (pickLatticePoints K).ncard = (pickLatticePoints (interior K)).ncard +
    (pickLatticePoints (frontier K)).ncard := by
  have hL : (pickLatticePoints K).Finite := pick_lattice_preimage_finite hK
  have hI : (pickLatticePoints (interior K)).Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ K
    exact interior_subset hz
  have hB : (pickLatticePoints (frontier K)).Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ K
    exact hK.isClosed.frontier_subset hz
  have hset : pickLatticePoints K =
    pickLatticePoints (interior K) ∪ pickLatticePoints (frontier K) := by
    change pickCast ⁻¹' K = pickCast ⁻¹' interior K ∪ pickCast ⁻¹' frontier K
    rw [← Set.preimage_union]
    congr 1
    calc
      K = closure K := hK.isClosed.closure_eq.symm
      _ = interior K ∪ frontier K := closure_eq_interior_union_frontier K
  rw [hset, Set.ncard_union_eq _ hI hB]
  rw [Set.disjoint_left]
  intro z hzI hzB
  exact Set.disjoint_left.mp disjoint_interior_frontier hzI hzB

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_cut_union](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_cut_union (P : Set (Fin 2 → ℝ)) (a c : Fin 2 → ℝ) :
  (P ∩ pickHalfPlus a c) ∪ (P ∩ pickHalfMinus a c) = P := by
  ext x
  rw [Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff, pick_mem_halfPlus_iff,
    pick_mem_halfMinus_iff]
  constructor
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  · intro hx
    obtain hpos | hneg := le_total 0 (pickSide a c x)
    · exact Or.inl ⟨hx, hpos⟩
    · exact Or.inr ⟨hx, hneg⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_cut_inter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_cut_inter {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
  {a c : Fin 2 → ℝ} (hac : a ≠ c) (ha : a ∈ P.extremePoints ℝ)
  (hc : c ∈ P.extremePoints ℝ) :
  (P ∩ pickHalfPlus a c) ∩ (P ∩ pickHalfMinus a c) = segment ℝ a c := by
  ext x
  constructor
  · rintro ⟨⟨hxP, hxplus⟩, -, hxminus⟩
    rw [← pick_inter_line_eq_segment hP hac ha hc]
    refine ⟨hxP, ?_⟩
    rw [← pick_half_inter_eq_line hac]
    exact ⟨hxplus, hxminus⟩
  · intro hx
    have hx' : x ∈ P ∩ (line[ℝ, a, c] : Set (Fin 2 → ℝ)) := by
      rwa [pick_inter_line_eq_segment hP hac ha hc]
    have hxhalf : x ∈ pickHalfPlus a c ∩ pickHalfMinus a c := by
      rwa [pick_half_inter_eq_line hac]
    exact ⟨⟨hx'.1, hxhalf.1⟩, hx'.1, hxhalf.2⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_volume_cut](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_volume_cut {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
  (hPcomp : IsCompact P) {a c : Fin 2 → ℝ} (hac : a ≠ c)
  (ha : a ∈ P.extremePoints ℝ) (hc : c ∈ P.extremePoints ℝ) :
  (volume P).toReal = (volume (P ∩ pickHalfPlus a c)).toReal +
    (volume (P ∩ pickHalfMinus a c)).toReal := by
  let Pp := P ∩ pickHalfPlus a c
  let Pm := P ∩ pickHalfMinus a c
  have hPp : IsCompact Pp := hPcomp.inter_right (pick_halfPlus_isClosed a c)
  have hPm : IsCompact Pm := hPcomp.inter_right (pick_halfMinus_isClosed a c)
  have hnull : volume (Pp ∩ Pm) = 0 := by
    rw [show Pp ∩ Pm = segment ℝ a c from pick_cut_inter hP hac ha hc]
    apply MeasureTheory.measure_mono_null _
      (volume.addHaar_affineSubspace line[ℝ, a, c] (pick_line_ne_top hac))
    intro x hx
    rw [← affineSegment_eq_segment ℝ] at hx
    exact affineSegment_subset_affineSpan ℝ a c hx
  have hmeasure := MeasureTheory.measure_union_add_inter (μ := volume) Pp
    hPm.isClosed.measurableSet
  rw [show Pp ∪ Pm = P from pick_cut_union P a c, hnull, add_zero] at hmeasure
  have hpfin : volume Pp ≠ ⊤ := ne_of_lt hPp.measure_lt_top
  have hmfin : volume Pm ≠ ⊤ := ne_of_lt hPm.measure_lt_top
  change (volume P).toReal = (volume Pp).toReal + (volume Pm).toReal
  rw [hmeasure, ENNReal.toReal_add hpfin hmfin]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_latticePoints_vadd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_latticePoints_vadd (p : Fin 2 → ℤ) (K : Set (Fin 2 → ℝ)) :
  pickLatticePoints (pickCast p +ᵥ K) =
    (fun z : Fin 2 → ℤ ↦ p + z) '' pickLatticePoints K := by
  ext z
  constructor
  · intro hz
    change pickCast z ∈ pickCast p +ᵥ K at hz
    obtain ⟨x, hx, hpx⟩ := hz
    refine ⟨z - p, ?_, ?_⟩
    · change pickCast (z - p) ∈ K
      have heq : pickCast (z - p) = x := by
        ext i
        have hi := congrFun hpx i
        change (p i : ℝ) + x i = (z i : ℝ) at hi
        change (z i - p i : ℤ) = x i
        norm_num
        linarith
      rwa [heq]
    · funext i
      simp
  · rintro ⟨q, hq, rfl⟩
    change pickCast (p + q) ∈ pickCast p +ᵥ K
    refine ⟨pickCast q, hq, ?_⟩
    ext i
    simp [pickCast]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_lattice_ncard_vadd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_lattice_ncard_vadd (p : Fin 2 → ℤ) (K : Set (Fin 2 → ℝ)) :
  (pickLatticePoints (pickCast p +ᵥ K)).ncard = (pickLatticePoints K).ncard := by
  rw [pick_latticePoints_vadd]
  exact Set.ncard_image_of_injective _ (Equiv.addLeft p).injective

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_invariant_vadd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_invariant_vadd (p : Fin 2 → ℤ) (K : Set (Fin 2 → ℝ)) :
  pickInvariant (pickCast p +ᵥ K) = pickInvariant K := by
  rw [pickInvariant, pickInvariant, pick_lattice_ncard_vadd, interior_vadd,
    pick_lattice_ncard_vadd]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_volume_vadd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_volume_vadd (p : Fin 2 → ℤ) (K : Set (Fin 2 → ℝ)) :
  (volume (pickCast p +ᵥ K)).toReal = (volume K).toReal := by
  rw [MeasureTheory.measure_vadd]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_radon_parts_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_radon_parts_two {f : Fin 4 → (Fin 2 → ℝ)}
  (hf : ConvexIndependent ℝ f) {I : Set (Fin 4)}
  (hI : (convexHull ℝ (f '' I) ∩ convexHull ℝ (f '' Iᶜ)).Nonempty) :
  I.ncard = 2 ∧ Iᶜ.ncard = 2 := by
  obtain ⟨y, hyI, hyIc⟩ := hI
  have hnontrivial (J : Set (Fin 4)) (hyJ : y ∈ convexHull ℝ (f '' J))
    (hyJc : y ∈ convexHull ℝ (f '' Jᶜ)) : J.Nontrivial := by
    have hJ : J.Nonempty := by
      apply Set.image_nonempty.mp
      exact convexHull_nonempty_iff.mp ⟨y, hyJ⟩
    obtain ⟨i, hi⟩ := hJ
    refine (Set.nontrivial_iff_exists_ne hi).2 ?_
    by_contra h
    push Not at h
    have hJeq : J = {i} := by
      ext j
      constructor
      · intro hj
        exact Set.mem_singleton_iff.mpr (h j hj)
      · intro hj
        rw [Set.mem_singleton_iff] at hj
        simpa [hj] using hi
    have hyi : y = f i := by
      rw [hJeq, Set.image_singleton, convexHull_singleton] at hyJ
      exact Set.mem_singleton_iff.mp hyJ
    subst y
    exact ((hf.mem_convexHull_iff Jᶜ i).mp hyJc) hi
  have hnI : I.Nontrivial := hnontrivial I hyI hyIc
  have hnIc : Iᶜ.Nontrivial := hnontrivial Iᶜ hyIc (by simpa using hyI)
  have hloI : 2 ≤ I.ncard := (Set.one_lt_ncard_iff_nontrivial.mpr hnI)
  have hloIc : 2 ≤ Iᶜ.ncard := (Set.one_lt_ncard_iff_nontrivial.mpr hnIc)
  have hsum : I.ncard + Iᶜ.ncard = 4 := by
    simpa using Set.ncard_add_ncard_compl I
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pick_not_collinear_of_convexIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_not_collinear_of_convexIndependent {f : Fin 4 → (Fin 2 → ℝ)}
  (hf : ConvexIndependent ℝ f) {i j k : Fin 4}
  (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
  ¬Collinear ℝ ({f i, f j, f k} : Set (Fin 2 → ℝ)) := by
  intro hcol
  obtain hijk | hjki | hkij := hcol.wbtw_or_wbtw_or_wbtw
  · have hjmem : f j ∈ convexHull ℝ (f '' ({i, k} : Set (Fin 4))) := by
    rwa [Set.image_pair, convexHull_pair]
    have := (hf.mem_convexHull_iff ({i, k} : Set (Fin 4)) j).mp hjmem
    simp [hij.symm, hjk] at this
  · have hkmem : f k ∈ convexHull ℝ (f '' ({j, i} : Set (Fin 4))) := by
    rwa [Set.image_pair, convexHull_pair]
    have := (hf.mem_convexHull_iff ({j, i} : Set (Fin 4)) k).mp hkmem
    simp [hjk.symm, hik.symm] at this
  · have himem : f i ∈ convexHull ℝ (f '' ({k, j} : Set (Fin 4))) := by
    rwa [Set.image_pair, convexHull_pair]
    have := (hf.mem_convexHull_iff ({k, j} : Set (Fin 4)) i).mp himem
    simp [hik, hij] at this

end MetaMathlibExt

/--
[_root_.MeasureTheory.toReal_volume_convexHull_lattice_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma MeasureTheory_toReal_volume_convexHull_lattice_triangle_eq
  {u v : Fin 2 → ℤ}
-- given
  (h : u 0 * v 1 - u 1 * v 0 ≠ 0) :
-- imply
  (volume (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
    Set (Fin 2 → ℝ)))).toReal =
    (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
    interior (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
    Set (Fin 2 → ℝ)))} : ℝ) +
    (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
    frontier (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
    Set (Fin 2 → ℝ)))} : ℝ) / 2 - 1 := by
-- proof
  apply MeasureTheory.toReal_volume_convexHull_lattice_triangle u v h

/--
[pick_convex_lattice_polygon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_convex_lattice_polygon_eq
  {vertices : Finset (Fin 2 → ℤ)}
-- given
  (hfull : (interior (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
-- imply
  (volume
    (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).toReal =
    (Set.ncard {z : Fin 2 → ℤ |
    (fun i => (z i : ℝ)) ∈
    interior
    (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))} : ℝ) +
    (Set.ncard {z : Fin 2 → ℤ |
    (fun i => (z i : ℝ)) ∈
    frontier
    (convexHull ℝ
    ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))} : ℝ) / 2 - 1 := by
-- proof
  apply MetaMathlibExt.pick_convex_lattice_polygon vertices hfull


-- created on 2026-10-20
-- updated on 2026-10-23
