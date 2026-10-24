/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.ZMultiples

/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/

namespace MetaMathlibExt

open Filter MeasureTheory
open scoped Pointwise

private abbrev pickCast (z : Fin 2 → ℤ) : Fin 2 → ℝ := fun i ↦ z i

private theorem pick_cast_injective : Function.Injective pickCast := by
  intro x y hxy
  ext i
  exact_mod_cast congrFun hxy i

private def pickVecs (u v : Fin 2 → ℤ) : Fin 2 → Fin 2 → ℝ := ![pickCast u, pickCast v]

private def pickMatrix (u v : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (pickVecs u v)

private def pickDet (u v : Fin 2 → ℤ) : ℤ := u 0 * v 1 - u 1 * v 0

private theorem pick_matrix_det (u v : Fin 2 → ℤ) :
    (pickMatrix u v).det = (pickDet u v : ℝ) := by
  simp [pickMatrix, pickVecs, pickDet, pickCast, Matrix.det_fin_two]

private noncomputable def pickBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
  let A := (pickMatrix u v).transpose
  let e : (Fin 2 → ℝ) ≃ₗ[ℝ] Fin 2 → ℝ :=
    Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 2)) A <| by
      rw [isUnit_iff_ne_zero, Matrix.det_transpose, pick_matrix_det]
      exact_mod_cast h
  (Pi.basisFun ℝ (Fin 2)).map e

private theorem pick_basis_apply (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) (i : Fin 2) :
    pickBasis u v h i = pickVecs u v i := by
  rw [pickBasis, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one]
  ext j
  simp [pickMatrix, pickVecs, pickCast]

private theorem pick_matrix_of_basis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Matrix.of (pickBasis u v h) = pickMatrix u v := by
  ext i j
  simp [pick_basis_apply, pickMatrix]

private noncomputable def pickTrianglePoints (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Fin 3 → Fin 2 → ℝ := ![0, pickBasis u v h 0, pickBasis u v h 1]

private theorem pick_trianglePoints_affineIndependent (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : AffineIndependent ℝ (pickTrianglePoints u v h) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
  let e := finSuccAboveEquiv (0 : Fin 3)
  have hli := (pickBasis u v h).linearIndependent.comp e.symm e.symm.injective
  convert hli using 1
  funext q
  rcases q with ⟨j, hj⟩
  fin_cases j
  · simp at hj
  · simp only [pickTrianglePoints, Function.comp_apply, vsub_eq_sub, sub_zero,
      Matrix.cons_val_zero]
    apply congrArg (pickBasis u v h)
    symm
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  · simp only [pickTrianglePoints, Function.comp_apply, vsub_eq_sub, sub_zero,
      Matrix.cons_val_zero]
    apply congrArg (pickBasis u v h)
    symm
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl

private noncomputable def pickAffineBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    AffineBasis (Fin 3) ℝ (Fin 2 → ℝ) :=
  let t : Affine.Simplex ℝ (Fin 2 → ℝ) 2 :=
    ⟨pickTrianglePoints u v h, pick_trianglePoints_affineIndependent u v h⟩
  AffineBasis.mk (pickTrianglePoints u v h) (pick_trianglePoints_affineIndependent u v h)
    (t.affineSpan_eq_top (by simp))

private theorem pick_affineBasis_basisOf_zero (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    ((pickAffineBasis u v h).basisOf 0).reindex
        (finSuccAboveEquiv (0 : Fin 3)).symm = pickBasis u v h := by
  ext i x
  fin_cases i <;>
    simp [Module.Basis.reindex_apply, pickTrianglePoints, finSuccAboveEquiv_apply,
      pick_basis_apply, pickVecs, pickCast]

private theorem pick_affineBasis_coord_succ (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) (x : Fin 2 → ℝ) :
    (pickAffineBasis u v h).coord (Fin.succ i) x = (pickBasis u v h).repr x i := by
  let e := finSuccAboveEquiv (0 : Fin 3)
  have he : (e i : Fin 3) = Fin.succ i := by simp [e, finSuccAboveEquiv_apply]
  rw [← he]
  calc
    (pickAffineBasis u v h).coord (e i) x =
        ((pickAffineBasis u v h).basisOf 0).repr x (e i) :=
      pick_coord_eq_basisOf_repr _ (by simp [pickTrianglePoints]) (e i) x
    _ = (((pickAffineBasis u v h).basisOf 0).reindex e.symm).repr x i := by
      simp [Module.Basis.repr_reindex]
    _ = (pickBasis u v h).repr x i := by rw [pick_affineBasis_basisOf_zero]

private noncomputable def pickTriangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Set (Fin 2 → ℝ) := convexHull ℝ (Set.range (pickAffineBasis u v h))

private theorem pick_mem_triangle_iff (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) :
    x ∈ pickTriangle u v h ↔
      0 ≤ (pickBasis u v h).repr x 0 ∧
        0 ≤ (pickBasis u v h).repr x 1 ∧
          (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 ≤ 1 := by
  rw [pickTriangle, (pickAffineBasis u v h).convexHull_eq_nonneg_coord]
  have hsum :
      (pickAffineBasis u v h).coord 0 x +
          ∑ i : Fin 2, (pickAffineBasis u v h).coord (Fin.succ i) x = 1 := by
    simpa only [Fin.sum_univ_succ] using (pickAffineBasis u v h).sum_coord_apply_eq_one x
  have hsum' :
      (pickAffineBasis u v h).coord 0 x + ∑ i : Fin 2, (pickBasis u v h).repr x i = 1 := by
    simpa only [pick_affineBasis_coord_succ] using hsum
  rw [Fin.sum_univ_two] at hsum'
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← pick_affineBasis_coord_succ u v h 0 x] using hx (Fin.succ 0)
    · simpa only [← pick_affineBasis_coord_succ u v h 1 x] using hx (Fin.succ 1)
    · linarith [hx 0]
  · rintro ⟨h0, h1, hsumle⟩
    refine Fin.cases (by linarith) (fun i ↦ ?_)
    rw [pick_affineBasis_coord_succ]
    fin_cases i
    · exact h0
    · exact h1

private theorem pick_mem_interior_triangle_iff (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) (x : Fin 2 → ℝ) :
    x ∈ interior (pickTriangle u v h) ↔
      0 < (pickBasis u v h).repr x 0 ∧
        0 < (pickBasis u v h).repr x 1 ∧
          (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 < 1 := by
  rw [pickTriangle, (pickAffineBasis u v h).interior_convexHull]
  have hsum :
      (pickAffineBasis u v h).coord 0 x +
          ∑ i : Fin 2, (pickAffineBasis u v h).coord (Fin.succ i) x = 1 := by
    simpa only [Fin.sum_univ_succ] using (pickAffineBasis u v h).sum_coord_apply_eq_one x
  have hsum' :
      (pickAffineBasis u v h).coord 0 x + ∑ i : Fin 2, (pickBasis u v h).repr x i = 1 := by
    simpa only [pick_affineBasis_coord_succ] using hsum
  rw [Fin.sum_univ_two] at hsum'
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← pick_affineBasis_coord_succ u v h 0 x] using hx (Fin.succ 0)
    · simpa only [← pick_affineBasis_coord_succ u v h 1 x] using hx (Fin.succ 1)
    · linarith [hx 0]
  · rintro ⟨h0, h1, hsumlt⟩
    refine Fin.cases (by linarith) (fun i ↦ ?_)
    rw [pick_affineBasis_coord_succ]
    fin_cases i
    · exact h0
    · exact h1

private noncomputable def pickReflect (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  pickBasis u v h 0 + pickBasis u v h 1 - x

private theorem pick_reflect_cast (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickReflect u v h (pickCast z) = pickCast (u + v - z) := by
  ext i
  simp [pickReflect, pick_basis_apply, pickVecs, pickCast]

private theorem pick_mem_reflected_triangle_iff (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) (x : Fin 2 → ℝ) :
    x ∈ pickReflect u v h '' pickTriangle u v h ↔
      (pickBasis u v h).repr x 0 ≤ 1 ∧
        (pickBasis u v h).repr x 1 ≤ 1 ∧
          1 ≤ (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 := by
  rw [pick_mem_reflect_image_iff, pick_mem_triangle_iff,
    pick_repr_reflect, pick_repr_reflect]
  constructor <;> rintro ⟨h0, h1, hsum⟩ <;> constructor
  · linarith
  · constructor <;> linarith
  · linarith
  · constructor <;> linarith

private theorem pick_parallelepiped_eq_union (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    parallelepiped (pickBasis u v h) =
      pickTriangle u v h ∪ pickReflect u v h '' pickTriangle u v h := by
  rw [parallelepiped_basis_eq]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro hx
    have hx0 := hx 0
    have hx1 := hx 1
    rcases le_total ((pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1) 1 with
      hsum | hsum
    · left
      exact (pick_mem_triangle_iff u v h x).2 ⟨hx0.1, hx1.1, hsum⟩
    · right
      exact (pick_mem_reflected_triangle_iff u v h x).2 ⟨hx0.2, hx1.2, hsum⟩
  · rintro (hx | hx) i
    · obtain ⟨h0, h1, hsum⟩ := (pick_mem_triangle_iff u v h x).1 hx
      fin_cases i
      · change 0 ≤ (pickBasis u v h).repr x 0 ∧ (pickBasis u v h).repr x 0 ≤ 1
        constructor <;> linarith
      · change 0 ≤ (pickBasis u v h).repr x 1 ∧ (pickBasis u v h).repr x 1 ≤ 1
        constructor <;> linarith
    · obtain ⟨h0, h1, hsum⟩ := (pick_mem_reflected_triangle_iff u v h x).1 hx
      fin_cases i
      · change 0 ≤ (pickBasis u v h).repr x 0 ∧ (pickBasis u v h).repr x 0 ≤ 1
        constructor <;> linarith
      · change 0 ≤ (pickBasis u v h).repr x 1 ∧ (pickBasis u v h).repr x 1 ≤ 1
        constructor <;> linarith

private noncomputable def pickDiagonal (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    AffineSubspace ℝ (Fin 2 → ℝ) :=
  AffineSubspace.mk' (pickBasis u v h 0) (LinearMap.ker (pickBasis u v h).sumCoords)

private theorem pick_triangle_inter_reflect_subset_diagonal (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickTriangle u v h ∩ (pickReflect u v h '' pickTriangle u v h) ⊆ pickDiagonal u v h := by
  rintro x ⟨hx, hrx⟩
  obtain ⟨-, -, hle⟩ := (pick_mem_triangle_iff u v h x).1 hx
  obtain ⟨-, -, hge⟩ := (pick_mem_reflected_triangle_iff u v h x).1 hrx
  exact (pick_mem_diagonal_iff u v h x).2 (le_antisymm hle hge)

private theorem pick_volume_triangle_inter_reflect (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    volume (pickTriangle u v h ∩ (pickReflect u v h '' pickTriangle u v h)) = 0 := by
  exact MeasureTheory.measure_mono_null (pick_triangle_inter_reflect_subset_diagonal u v h)
    (volume.addHaar_affineSubspace (pickDiagonal u v h) (pick_diagonal_ne_top u v h))

private theorem pick_two_volume_triangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    volume (pickTriangle u v h) + volume (pickTriangle u v h) =
      ENNReal.ofReal |(pickDet u v : ℝ)| := by
  calc
    volume (pickTriangle u v h) + volume (pickTriangle u v h) =
        volume (pickTriangle u v h) +
          volume (pickReflect u v h '' pickTriangle u v h) := by
      rw [pick_volume_reflected_triangle]
    _ = volume (pickTriangle u v h ∪ pickReflect u v h '' pickTriangle u v h) := by
      have hunion := measure_union_add_inter (μ := volume) (pickTriangle u v h)
        (pick_reflected_triangle_measurableSet u v h)
      rw [pick_volume_triangle_inter_reflect, add_zero] at hunion
      exact hunion.symm
    _ = volume (parallelepiped (pickBasis u v h)) := by
      rw [pick_parallelepiped_eq_union]
    _ = volume (ZSpan.fundamentalDomain (pickBasis u v h)) := by
      exact (ZSpan.fundamentalDomain_ae_parallelepiped (pickBasis u v h) volume).measure_eq.symm
    _ = ENNReal.ofReal |(pickDet u v : ℝ)| := by
      rw [ZSpan.volume_fundamentalDomain, pick_matrix_of_basis, pick_matrix_det]

private theorem pick_volume_triangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (volume (pickTriangle u v h)).toReal = |(pickDet u v : ℝ)| / 2 := by
  have hfinite : volume (pickTriangle u v h) ≠ ⊤ :=
    ne_of_lt (pick_triangle_isCompact u v h).measure_lt_top
  have hre := congrArg ENNReal.toReal (pick_two_volume_triangle u v h)
  rw [ENNReal.toReal_add hfinite hfinite, ENNReal.toReal_ofReal (abs_nonneg _)] at hre
  linarith

private def pickIntMatrix (u v : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of ![u, v]

private theorem pick_intMatrix_det (u v : Fin 2 → ℤ) :
    (pickIntMatrix u v).det = pickDet u v := by
  simp [pickIntMatrix, pickDet, Matrix.det_fin_two]

private def pickIntMap (u v : Fin 2 → ℤ) : (Fin 2 → ℤ) →ₗ[ℤ] Fin 2 → ℤ :=
  Matrix.toLin' (pickIntMatrix u v).transpose

private theorem pick_intMap_injective (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Function.Injective (pickIntMap u v) := by
  apply Matrix.mulVec_injective_of_det_ne_zero
  rw [Matrix.det_transpose, pick_intMatrix_det]
  exact h

private def pickSublattice (u v : Fin 2 → ℤ) : AddSubgroup (Fin 2 → ℤ) :=
  (pickIntMap u v).toAddMonoidHom.range

private noncomputable def pickSublatticeBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Module.Basis (Fin 2) ℤ (pickSublattice u v) :=
  let g : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) := (pickIntMap u v).toAddMonoidHom
  let f : (Fin 2 → ℤ) →+ pickSublattice u v := g.rangeRestrict
  let e : (Fin 2 → ℤ) ≃+ pickSublattice u v := AddEquiv.ofBijective f ⟨by
    intro x y hxy
    exact pick_intMap_injective u v h (congrArg Subtype.val hxy), g.rangeRestrict_surjective⟩
  (Pi.basisFun ℤ (Fin 2)).map e.toIntLinearEquiv

private theorem pick_sublattice_index (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickSublattice u v).index = (pickDet u v).natAbs := by
  rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)) (pickSublattice u v)
    (pickSublatticeBasis u v h), Module.Basis.det_apply]
  have hmatrix :
      (Pi.basisFun ℤ (Fin 2)).toMatrix
          (fun i ↦ (pickSublatticeBasis u v h i : Fin 2 → ℤ)) =
        (pickIntMatrix u v).transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, pick_sublatticeBasis_apply, pickIntMatrix]
  rw [hmatrix, Matrix.det_transpose, pick_intMatrix_det]

private theorem pick_repr_cast_intMap (u v c : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) :
    (pickBasis u v h).repr (pickCast (pickIntMap u v c)) i = (c i : ℝ) := by
  have hcast :
      pickCast (pickIntMap u v c) =
        (c 0 : ℝ) • pickBasis u v h 0 + (c 1 : ℝ) • pickBasis u v h 1 := by
    ext j
    fin_cases j <;>
      simp [pickIntMap, pickIntMatrix, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, pickCast, pick_basis_apply, pickVecs] <;> ring
  rw [hcast, map_add, map_smul, map_smul, Module.Basis.repr_self,
    Module.Basis.repr_self]
  fin_cases i <;> simp

private noncomputable def pickFloorCoeffs (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Fin 2 → ℤ := fun i ↦ ⌊(pickBasis u v h).repr (pickCast z) i⌋

private noncomputable def pickFractInt (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Fin 2 → ℤ := z - pickIntMap u v (pickFloorCoeffs u v z h)

private theorem pick_repr_cast_fractInt (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) :
    (pickBasis u v h).repr (pickCast (pickFractInt u v z h)) i =
      Int.fract ((pickBasis u v h).repr (pickCast z) i) := by
  have hcast :
      pickCast (pickFractInt u v z h) =
        pickCast z - pickCast (pickIntMap u v (pickFloorCoeffs u v z h)) := by
    ext j
    simp [pickFractInt, pickCast]
  rw [hcast, map_sub, Finsupp.coe_sub, Pi.sub_apply, pick_repr_cast_intMap]
  rfl

private theorem pick_fractInt_mem_fundamentalDomain (u v z : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickCast (pickFractInt u v z h) ∈ ZSpan.fundamentalDomain (pickBasis u v h) := by
  rw [ZSpan.mem_fundamentalDomain]
  intro i
  rw [pick_repr_cast_fractInt]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

private theorem pick_cast_fractInt (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickCast (pickFractInt u v z h) = ZSpan.fract (pickBasis u v h) (pickCast z) := by
  apply (pickBasis u v h).ext_elem
  intro i
  rw [pick_repr_cast_fractInt, ZSpan.repr_fract_apply]

private theorem pick_cast_intMap_mem_zspan (u v c : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickCast (pickIntMap u v c) ∈ Submodule.span ℤ (Set.range (pickBasis u v h)) := by
  rw [(pickBasis u v h).mem_span_iff_repr_mem ℤ]
  intro i
  exact ⟨c i, (pick_repr_cast_intMap u v c h i).symm⟩

private theorem pick_fractInt_eq_of_rel (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    {z z' : Fin 2 → ℤ} (hrel : QuotientAddGroup.leftRel (pickSublattice u v) z z') :
    pickFractInt u v z h = pickFractInt u v z' h := by
  apply pick_cast_injective
  rw [pick_cast_fractInt, pick_cast_fractInt]
  apply (ZSpan.fract_eq_fract (pickBasis u v h) (pickCast z) (pickCast z')).2
  have hs : -z + z' ∈ pickSublattice u v := QuotientAddGroup.leftRel_apply.mp hrel
  rcases hs with ⟨c, hc⟩
  have hcast : -pickCast z + pickCast z' = pickCast (pickIntMap u v c) := by
    change -pickCast z + pickCast z' = pickCast ((pickIntMap u v).toAddMonoidHom c)
    rw [hc]
    ext i
    simp [pickCast]
  rw [hcast]
  exact pick_cast_intMap_mem_zspan u v c h

private noncomputable def pickFundamentalLatticePoints (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : Set (Fin 2 → ℤ) :=
  {z | pickCast z ∈ ZSpan.fundamentalDomain (pickBasis u v h)}

private noncomputable def pickQuotientToFundamental (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    ((Fin 2 → ℤ) ⧸ pickSublattice u v) → pickFundamentalLatticePoints u v h := fun q ↦
  Quotient.liftOn q
    (fun z ↦ ⟨pickFractInt u v z h, pick_fractInt_mem_fundamentalDomain u v z h⟩)
    (fun _ _ hrel ↦ Subtype.ext (pick_fractInt_eq_of_rel u v h hrel))

@[simp]
private theorem pick_quotientToFundamental_mk (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickQuotientToFundamental u v h (QuotientAddGroup.mk z) =
      ⟨pickFractInt u v z h, pick_fractInt_mem_fundamentalDomain u v z h⟩ := rfl

private theorem pick_quotient_fractInt_eq (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (QuotientAddGroup.mk (pickFractInt u v z h) : (Fin 2 → ℤ) ⧸ pickSublattice u v) =
      QuotientAddGroup.mk z := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  have hm : pickIntMap u v (pickFloorCoeffs u v z h) ∈ pickSublattice u v :=
    ⟨pickFloorCoeffs u v z h, rfl⟩
  convert (pickSublattice u v).neg_mem hm using 1
  simp [pickFractInt]

private theorem pick_fractInt_eq_self_of_mem (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (hz : pickCast z ∈ ZSpan.fundamentalDomain (pickBasis u v h)) :
    pickFractInt u v z h = z := by
  apply pick_cast_injective
  rw [pick_cast_fractInt]
  exact ZSpan.fract_eq_self.mpr hz

private theorem pick_quotientToFundamental_bijective (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : Function.Bijective (pickQuotientToFundamental u v h) := by
  constructor
  · intro q q' hq
    induction q using Quotient.inductionOn with
    | _ z =>
      induction q' using Quotient.inductionOn with
      | _ z' =>
        have hval : pickFractInt u v z h = pickFractInt u v z' h :=
          congrArg Subtype.val hq
        calc
          QuotientAddGroup.mk z = QuotientAddGroup.mk (pickFractInt u v z h) :=
            (pick_quotient_fractInt_eq u v z h).symm
          _ = QuotientAddGroup.mk (pickFractInt u v z' h) := congrArg QuotientAddGroup.mk hval
          _ = QuotientAddGroup.mk z' := pick_quotient_fractInt_eq u v z' h
  · rintro ⟨z, hz⟩
    refine ⟨QuotientAddGroup.mk z, ?_⟩
    apply Subtype.ext
    exact pick_fractInt_eq_self_of_mem u v z h hz

private noncomputable def pickQuotientFundamentalEquiv (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    ((Fin 2 → ℤ) ⧸ pickSublattice u v) ≃ pickFundamentalLatticePoints u v h :=
  Equiv.ofBijective (pickQuotientToFundamental u v h)
    (pick_quotientToFundamental_bijective u v h)

private theorem pick_fundamentalLatticePoints_ncard (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    (pickFundamentalLatticePoints u v h).ncard = (pickDet u v).natAbs := by
  calc
    (pickFundamentalLatticePoints u v h).ncard =
        Nat.card (pickFundamentalLatticePoints u v h) := by
      rw [← Set.ncard_coe, Set.ncard_univ]
    _ = Nat.card ((Fin 2 → ℤ) ⧸ pickSublattice u v) :=
      (Nat.card_congr (pickQuotientFundamentalEquiv u v h)).symm
    _ = (pickSublattice u v).index := (pickSublattice u v).index_eq_card.symm
    _ = (pickDet u v).natAbs := pick_sublattice_index u v h

private abbrev pickLatticePoints (K : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℤ) :=
  pickCast ⁻¹' K

private theorem pick_repr_cast_u (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickBasis u v h).repr (pickCast u) = Finsupp.single 0 1 := by
  have hu : pickBasis u v h 0 = pickCast u := by
    simp [pick_basis_apply, pickVecs]
  rw [← hu, Module.Basis.repr_self]

private theorem pick_repr_cast_v (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickBasis u v h).repr (pickCast v) = Finsupp.single 1 1 := by
  have hv : pickBasis u v h 1 = pickCast v := by
    simp [pick_basis_apply, pickVecs]
  rw [← hv, Module.Basis.repr_self]

private theorem pick_fundamental_inter_triangle (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickFundamentalLatticePoints u v h ∩ pickLatticePoints (pickTriangle u v h) =
      pickLatticePoints (pickTriangle u v h) \ {u, v} := by
  ext z
  constructor
  · rintro ⟨hzD, hzT⟩
    refine ⟨hzT, ?_⟩
    rintro (hzu | hzv)
    · have hcoord := (pick_mem_fundamentalDomain_iff u v h (pickCast z)).1 hzD
      rw [hzu, pick_repr_cast_u] at hcoord
      norm_num at hcoord
    · rw [Set.mem_singleton_iff] at hzv
      have hcoord := (pick_mem_fundamentalDomain_iff u v h (pickCast z)).1 hzD
      rw [hzv, pick_repr_cast_v] at hcoord
      norm_num at hcoord
  · rintro ⟨hzT, hzuv⟩
    obtain ⟨h0, h1, hsum⟩ := (pick_mem_triangle_iff u v h (pickCast z)).1 hzT
    have hzu : z ≠ u := fun hzu ↦ hzuv (by simp [hzu])
    have hzv : z ≠ v := fun hzv ↦ hzuv (by simp [hzv])
    have h0lt : (pickBasis u v h).repr (pickCast z) 0 < 1 := by
      apply lt_of_le_of_ne (by linarith)
      intro h0eq
      have h1eq : (pickBasis u v h).repr (pickCast z) 1 = 0 := by linarith
      apply hzu
      apply pick_cast_injective
      apply (pickBasis u v h).repr.injective
      rw [pick_repr_cast_u]
      ext i
      fin_cases i <;> simp [h0eq, h1eq]
    have h1lt : (pickBasis u v h).repr (pickCast z) 1 < 1 := by
      apply lt_of_le_of_ne (by linarith)
      intro h1eq
      have h0eq : (pickBasis u v h).repr (pickCast z) 0 = 0 := by linarith
      apply hzv
      apply pick_cast_injective
      apply (pickBasis u v h).repr.injective
      rw [pick_repr_cast_v]
      ext i
      fin_cases i <;> simp [h0eq, h1eq]
    exact ⟨(pick_mem_fundamentalDomain_iff u v h (pickCast z)).2
      ⟨h0, h0lt, h1, h1lt⟩, hzT⟩

private def pickIntReflect (u v z : Fin 2 → ℤ) : Fin 2 → ℤ := u + v - z

private theorem pick_intReflect_mem_interior_iff (u v z : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    z ∈ pickFundamentalLatticePoints u v h \ pickLatticePoints (pickTriangle u v h) ↔
      pickIntReflect u v z ∈ pickLatticePoints (interior (pickTriangle u v h)) := by
  let a := (pickBasis u v h).repr (pickCast z) 0
  let b := (pickBasis u v h).repr (pickCast z) 1
  have hreflect : pickCast (pickIntReflect u v z) = pickReflect u v h (pickCast z) := by
    exact (pick_reflect_cast u v z h).symm
  constructor
  · rintro ⟨hzD, hzT⟩
    obtain ⟨ha0, ha1, hb0, hb1⟩ :=
      (pick_mem_fundamentalDomain_iff u v h (pickCast z)).1 hzD
    have hab : 1 < a + b := by
      apply lt_of_not_ge
      intro hab
      exact hzT ((pick_mem_triangle_iff u v h (pickCast z)).2 ⟨ha0, hb0, hab⟩)
    change pickCast (pickIntReflect u v z) ∈ interior (pickTriangle u v h)
    rw [hreflect, pick_mem_interior_triangle_iff, pick_repr_reflect, pick_repr_reflect]
    exact ⟨by linarith, by linarith, by dsimp only [a, b] at hab ⊢; linarith⟩
  · intro hzI
    change pickCast (pickIntReflect u v z) ∈ interior (pickTriangle u v h) at hzI
    rw [hreflect, pick_mem_interior_triangle_iff, pick_repr_reflect,
      pick_repr_reflect] at hzI
    obtain ⟨ha, hb, hab⟩ := hzI
    have ha0 : 0 ≤ a := by dsimp only [a] at ha ⊢; linarith
    have ha1 : a < 1 := by dsimp only [a] at ha ⊢; linarith
    have hb0 : 0 ≤ b := by dsimp only [b] at hb ⊢; linarith
    have hb1 : b < 1 := by dsimp only [b] at hb ⊢; linarith
    have hab' : 1 < a + b := by dsimp only [a, b] at hab ⊢; linarith
    refine ⟨(pick_mem_fundamentalDomain_iff u v h (pickCast z)).2
      ⟨ha0, ha1, hb0, hb1⟩, ?_⟩
    intro hzT
    have hsum := ((pick_mem_triangle_iff u v h (pickCast z)).1 hzT).2.2
    dsimp only [a, b] at hab'
    linarith

private theorem pick_intReflect_bijOn (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Set.BijOn (pickIntReflect u v)
      (pickFundamentalLatticePoints u v h \ pickLatticePoints (pickTriangle u v h))
      (pickLatticePoints (interior (pickTriangle u v h))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (pick_intReflect_mem_interior_iff u v z h).1 hz
  · intro z _ z' _ hzz'
    have := congrArg (pickIntReflect u v) hzz'
    simpa using this
  · intro z hz
    refine ⟨pickIntReflect u v z, ?_, by simp⟩
    apply (pick_intReflect_mem_interior_iff u v (pickIntReflect u v z) h).2
    simpa using hz

private theorem pick_triangle_lattice_count (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickDet u v).natAbs + 2 =
      2 * (pickLatticePoints (interior (pickTriangle u v h))).ncard +
        (pickLatticePoints (frontier (pickTriangle u v h))).ncard := by
  let F := pickFundamentalLatticePoints u v h
  let L := pickLatticePoints (pickTriangle u v h)
  let I := pickLatticePoints (interior (pickTriangle u v h))
  let B := pickLatticePoints (frontier (pickTriangle u v h))
  have hF : F.Finite := pick_fundamentalLatticePoints_finite u v h
  have hL : L.Finite := pick_triangleLatticePoints_finite u v h
  have hI : I.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ pickTriangle u v h
    exact interior_subset hz
  have hB : B.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ pickTriangle u v h
    exact (pick_triangle_isCompact u v h).isClosed.frontier_subset hz
  have hsplitDisjoint : Disjoint (F ∩ L) (F \ L) := by
    rw [Set.disjoint_left]
    exact fun _ hx hy ↦ hy.2 hx.2
  have hsplit : F.ncard = (F ∩ L).ncard + (F \ L).ncard := by
    calc
      F.ncard = ((F ∩ L) ∪ (F \ L)).ncard := by rw [Set.inter_union_sdiff]
      _ = (F ∩ L).ncard + (F \ L).ncard :=
        Set.ncard_union_eq hsplitDisjoint (hF.inter_of_left L) hF.sdiff
  have hreflect : (F \ L).ncard = I.ncard := by
    exact (pick_intReflect_bijOn u v h).ncard_eq
  have huL : u ∈ L := by
    change pickCast u ∈ pickTriangle u v h
    rw [pick_mem_triangle_iff, pick_repr_cast_u]
    norm_num
  have hvL : v ∈ L := by
    change pickCast v ∈ pickTriangle u v h
    rw [pick_mem_triangle_iff, pick_repr_cast_v]
    norm_num
  have huvL : {u, v} ⊆ L := by
    rintro z (rfl | hz)
    · exact huL
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hvL
  have hinter : (F ∩ L).ncard + 2 = L.ncard := by
    rw [pick_fundamental_inter_triangle u v h]
    calc
      (L \ {u, v}).ncard + 2 =
          (L \ {u, v}).ncard + ({u, v} : Set (Fin 2 → ℤ)).ncard := by
        rw [Set.ncard_pair (pick_u_ne_v u v h)]
      _ = L.ncard := Set.ncard_sdiff_add_ncard_of_subset huvL hL
  have hdecomp : L = I ∪ B := by
    change pickCast ⁻¹' pickTriangle u v h =
      pickCast ⁻¹' interior (pickTriangle u v h) ∪
        pickCast ⁻¹' frontier (pickTriangle u v h)
    rw [← Set.preimage_union]
    congr 1
    calc
      pickTriangle u v h = closure (pickTriangle u v h) :=
        (pick_triangle_isCompact u v h).isClosed.closure_eq.symm
      _ = interior (pickTriangle u v h) ∪ frontier (pickTriangle u v h) :=
        closure_eq_interior_union_frontier _
  have hIBdisjoint : Disjoint I B := by
    rw [Set.disjoint_left]
    intro z hzI hzB
    exact Set.disjoint_left.mp disjoint_interior_frontier hzI hzB
  have hLB : L.ncard = I.ncard + B.ncard := by
    rw [hdecomp, Set.ncard_union_eq hIBdisjoint hI hB]
  have hFcard : F.ncard = (pickDet u v).natAbs :=
    pick_fundamentalLatticePoints_ncard u v h
  dsimp only [F, L, I, B] at hsplit hreflect hinter hLB hFcard ⊢
  omega

private theorem pick_triangle_eq_explicit (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickTriangle u v h = convexHull ℝ ({0, pickCast u, pickCast v} : Set (Fin 2 → ℝ)) := by
  unfold pickTriangle
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rw [pick_affineBasis_apply]
    fin_cases i <;> simp [pickTrianglePoints, pick_basis_apply, pickVecs]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp [pickTrianglePoints]⟩
    · refine ⟨1, ?_⟩
      simp [pickTrianglePoints, pick_basis_apply, pickVecs]
    · refine ⟨2, ?_⟩
      simp [pickTrianglePoints, pick_basis_apply, pickVecs]

/-- Pick's area formula for a nondegenerate triangle with one vertex at the origin and the other
two vertices in the standard integer lattice. -/
theorem _root_.MeasureTheory.toReal_volume_convexHull_lattice_triangle (u v : Fin 2 → ℤ)
    (h : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    (volume (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
      Set (Fin 2 → ℝ)))).toReal =
      (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
        interior (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
          Set (Fin 2 → ℝ)))} : ℝ) +
      (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
        frontier (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
          Set (Fin 2 → ℝ)))} : ℝ) / 2 - 1 := by
  have hdet : pickDet u v ≠ 0 := h
  rw [← pick_triangle_eq_explicit u v hdet]
  have hcount := pick_triangle_lattice_count u v hdet
  rw [pick_volume_triangle u v hdet]
  have habs : |(pickDet u v : ℝ)| = ((pickDet u v).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  have hcountR := congrArg (fun n : ℕ ↦ (n : ℝ)) hcount
  push_cast at hcountR
  change ((pickDet u v).natAbs : ℝ) + 2 =
    2 * (Set.ncard {z : Fin 2 → ℤ | pickCast z ∈
      interior (pickTriangle u v hdet)} : ℝ) +
      (Set.ncard {z : Fin 2 → ℤ | pickCast z ∈
        frontier (pickTriangle u v hdet)} : ℝ) at hcountR
  change ((pickDet u v).natAbs : ℝ) / 2 =
    (Set.ncard {z : Fin 2 → ℤ | pickCast z ∈
      interior (pickTriangle u v hdet)} : ℝ) +
      (Set.ncard {z : Fin 2 → ℤ | pickCast z ∈
        frontier (pickTriangle u v hdet)} : ℝ) / 2 - 1
  linarith

private noncomputable def pickNormal (a c : Fin 2 → ℝ) :
    StrongDual ℝ (Fin 2 → ℝ) :=
  (c 0 - a 0) • ContinuousLinearMap.proj 1 -
    (c 1 - a 1) • ContinuousLinearMap.proj 0

private noncomputable def pickSide (a c x : Fin 2 → ℝ) : ℝ :=
  pickNormal a c x - pickNormal a c a

private noncomputable def pickHalfPlus (a c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  pickNormal a c ⁻¹' Set.Ici (pickNormal a c a)

private noncomputable def pickHalfMinus (a c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  pickNormal a c ⁻¹' Set.Iic (pickNormal a c a)

private theorem pick_lattice_segment_ncard {A C : Fin 2 → ℤ} (hAC : A ≠ C) :
    (pickLatticePoints (segment ℝ (pickCast A) (pickCast C))).ncard =
      (pickLatticePoints (openSegment ℝ (pickCast A) (pickCast C))).ncard + 2 := by
  let O := pickLatticePoints (openSegment ℝ (pickCast A) (pickCast C))
  have hset : pickLatticePoints (segment ℝ (pickCast A) (pickCast C)) = {A, C} ∪ O := by
    change pickCast ⁻¹' segment ℝ (pickCast A) (pickCast C) = {A, C} ∪ O
    dsimp only [O]
    rw [← insert_endpoints_openSegment ℝ]
    ext z
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [pick_cast_injective.eq_iff, pick_cast_injective.eq_iff]
    tauto
  have hdisj : Disjoint ({A, C} : Set (Fin 2 → ℤ)) O := by
    rw [Set.disjoint_left]
    intro z hz hzO
    rcases hz with hza | hzc
    · rw [hza] at hzO
      apply hAC
      apply pick_cast_injective
      exact left_mem_openSegment_iff.mp hzO
    · rw [Set.mem_singleton_iff] at hzc
      rw [hzc] at hzO
      apply hAC
      apply pick_cast_injective
      exact right_mem_openSegment_iff.mp hzO
  have hO : O.Finite := by
    have hpair : ({pickCast A, pickCast C} : Set (Fin 2 → ℝ)).Finite :=
      Set.finite_insert.mpr (Set.finite_singleton _)
    have hseg : IsCompact (segment ℝ (pickCast A) (pickCast C)) := by
      rw [← convexHull_pair]
      exact hpair.isCompact_convexHull ℝ
    apply (pick_lattice_preimage_finite hseg).subset
    intro z hz
    exact openSegment_subset_segment ℝ _ _ hz
  dsimp only [O] at hset hdisj hO ⊢
  rw [hset, Set.ncard_union_eq hdisj (Set.finite_insert.mpr (Set.finite_singleton C)) hO,
    Set.ncard_pair hAC]
  omega

private noncomputable def pickInvariant (K : Set (Fin 2 → ℝ)) : ℝ :=
  (pickLatticePoints K).ncard + (pickLatticePoints (interior K)).ncard - 2

private theorem pick_invariant_cut {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
    (hPcomp : IsCompact P) (hPint : (interior P).Nonempty) {A C : Fin 2 → ℤ}
    {b d y : Fin 2 → ℝ} (hAC : A ≠ C)
    (ha : pickCast A ∈ P.extremePoints ℝ) (hb : b ∈ P)
    (hc : pickCast C ∈ P.extremePoints ℝ) (hd : d ∈ P)
    (hyac : y ∈ openSegment ℝ (pickCast A) (pickCast C))
    (hybd : y ∈ openSegment ℝ b d) (hbline : b ∉ line[ℝ, pickCast A, pickCast C]) :
    pickInvariant P = pickInvariant (P ∩ pickHalfPlus (pickCast A) (pickCast C)) +
      pickInvariant (P ∩ pickHalfMinus (pickCast A) (pickCast C)) := by
  let a := pickCast A
  let c := pickCast C
  let Pp := P ∩ pickHalfPlus a c
  let Pm := P ∩ pickHalfMinus a c
  let L := pickLatticePoints P
  let Lp := pickLatticePoints Pp
  let Lm := pickLatticePoints Pm
  let I := pickLatticePoints (interior P)
  let Ip := pickLatticePoints (interior Pp)
  let Im := pickLatticePoints (interior Pm)
  let O := pickLatticePoints (openSegment ℝ a c)
  have hac : a ≠ c := fun hac ↦ hAC (pick_cast_injective hac)
  have hPpcomp : IsCompact Pp := hPcomp.inter_right (pick_halfPlus_isClosed a c)
  have hPmcomp : IsCompact Pm := hPcomp.inter_right (pick_halfMinus_isClosed a c)
  have hL : L.Finite := pick_lattice_preimage_finite hPcomp
  have hLp : Lp.Finite := pick_lattice_preimage_finite hPpcomp
  have hLm : Lm.Finite := pick_lattice_preimage_finite hPmcomp
  have hIp : Ip.Finite := by
    apply hLp.subset
    intro z hz
    change pickCast z ∈ Pp
    exact interior_subset hz
  have hIm : Im.Finite := by
    apply hLm.subset
    intro z hz
    change pickCast z ∈ Pm
    exact interior_subset hz
  have hI : I.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ P
    exact interior_subset hz
  have hO : O.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ P
    exact hP.segment_subset ha.1 hc.1 (openSegment_subset_segment ℝ a c hz)
  have hLunion : Lp ∪ Lm = L := by
    change pickCast ⁻¹' Pp ∪ pickCast ⁻¹' Pm = pickCast ⁻¹' P
    rw [← Set.preimage_union, pick_cut_union]
  have hLinter : Lp ∩ Lm = pickLatticePoints (segment ℝ a c) := by
    change pickCast ⁻¹' Pp ∩ pickCast ⁻¹' Pm = pickCast ⁻¹' segment ℝ a c
    rw [← Set.preimage_inter, pick_cut_inter hP hac ha hc]
  have hclosed := Set.ncard_union_add_ncard_inter Lp Lm hLp hLm
  rw [hLunion, hLinter] at hclosed
  have hsegment : (pickLatticePoints (segment ℝ a c)).ncard = O.ncard + 2 := by
    exact pick_lattice_segment_ncard hAC
  have hIset : I = (Ip ∪ Im) ∪ O := by
    change pickCast ⁻¹' interior P =
      (pickCast ⁻¹' interior Pp ∪ pickCast ⁻¹' interior Pm) ∪
        pickCast ⁻¹' openSegment ℝ a c
    rw [← Set.preimage_union, ← Set.preimage_union,
      pick_interior_cut hP hPint ha hb hc hd hac hyac hybd hbline]
  have hIpIm : Disjoint Ip Im := by
    rw [Set.disjoint_left]
    intro z hzp hzm
    have hp : pickNormal a c a < pickNormal a c (pickCast z) := by
      change pickCast z ∈ interior Pp at hzp
      rw [interior_inter, pick_interior_halfPlus hac] at hzp
      exact hzp.2
    have hm : pickNormal a c (pickCast z) < pickNormal a c a := by
      change pickCast z ∈ interior Pm at hzm
      rw [interior_inter, pick_interior_halfMinus hac] at hzm
      exact hzm.2
    linarith
  have hhalvesO : Disjoint (Ip ∪ Im) O := by
    rw [Set.disjoint_left]
    intro z hzhalf hzO
    have hzline : pickCast z ∈ line[ℝ, a, c] := by
      apply affineSegment_subset_affineSpan ℝ a c
      rw [affineSegment_eq_segment]
      exact openSegment_subset_segment ℝ a c hzO
    have hzeq : pickNormal a c (pickCast z) = pickNormal a c a := by
      have := (pick_side_eq_zero_iff_mem_line hac (pickCast z)).2 hzline
      dsimp only [pickSide] at this
      linarith
    rcases hzhalf with hzp | hzm
    · change pickCast z ∈ interior Pp at hzp
      rw [interior_inter, pick_interior_halfPlus hac] at hzp
      have hlt : pickNormal a c a < pickNormal a c (pickCast z) := hzp.2
      rw [hzeq] at hlt
      exact (lt_irrefl _ hlt).elim
    · change pickCast z ∈ interior Pm at hzm
      rw [interior_inter, pick_interior_halfMinus hac] at hzm
      have hlt : pickNormal a c (pickCast z) < pickNormal a c a := hzm.2
      rw [hzeq] at hlt
      exact (lt_irrefl _ hlt).elim
  have hhalfCard : (Ip ∪ Im).ncard = Ip.ncard + Im.ncard :=
    Set.ncard_union_eq hIpIm hIp hIm
  have hinter : I.ncard = Ip.ncard + Im.ncard + O.ncard := by
    rw [hIset, Set.ncard_union_eq hhalvesO (hIp.union hIm) hO, hhalfCard]
  have hclosedR := congrArg (fun n : ℕ ↦ (n : ℝ)) hclosed
  have hsegmentR := congrArg (fun n : ℕ ↦ (n : ℝ)) hsegment
  have hinterR := congrArg (fun n : ℕ ↦ (n : ℝ)) hinter
  push_cast at hclosedR hsegmentR hinterR
  change (L.ncard : ℝ) + I.ncard - 2 =
    ((Lp.ncard : ℝ) + Ip.ncard - 2) + ((Lm.ncard : ℝ) + Im.ncard - 2)
  linarith

private theorem pick_origin_triangle_doubled (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    2 * (volume (pickTriangle u v h)).toReal = pickInvariant (pickTriangle u v h) := by
  have hformula := toReal_volume_convexHull_lattice_triangle u v h
  rw [← pick_triangle_eq_explicit u v h] at hformula
  change (volume (pickTriangle u v h)).toReal =
    (pickLatticePoints (interior (pickTriangle u v h))).ncard +
      (pickLatticePoints (frontier (pickTriangle u v h))).ncard / 2 - 1 at hformula
  have hLB := pick_lattice_ncard_eq_interior_add_frontier (pick_triangle_isCompact u v h)
  have hLBR := congrArg (fun n : ℕ ↦ (n : ℝ)) hLB
  push_cast at hLBR
  rw [pickInvariant]
  change 2 * (volume (pickTriangle u v h)).toReal =
    (pickLatticePoints (pickTriangle u v h)).ncard +
      (pickLatticePoints (interior (pickTriangle u v h))).ncard - 2
  linarith

private theorem pick_triangle_doubled (p q r : Fin 2 → ℤ)
    (h : pickDet (q - p) (r - p) ≠ 0) :
    2 * (volume (convexHull ℝ
      ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)))).toReal =
      pickInvariant (convexHull ℝ
        ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ))) := by
  let T := pickTriangle (q - p) (r - p) h
  have hset : ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) =
      pickCast p +ᵥ ({0, pickCast (q - p), pickCast (r - p)} : Set (Fin 2 → ℝ)) := by
    rw [← Set.image_vadd]
    simp only [vadd_eq_add, Set.image_insert_eq, add_zero, Set.image_singleton]
    have hpq : pickCast p + pickCast (q - p) = pickCast q := by
      funext i
      simp [pickCast]
    have hpr : pickCast p + pickCast (r - p) = pickCast r := by
      funext i
      simp [pickCast]
    rw [hpq, hpr]
  have htriangle : convexHull ℝ
        ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) = pickCast p +ᵥ T := by
    rw [hset, convexHull_vadd]
    change pickCast p +ᵥ convexHull ℝ
      ({0, pickCast (q - p), pickCast (r - p)} : Set (Fin 2 → ℝ)) = pickCast p +ᵥ T
    rw [← pick_triangle_eq_explicit]
  rw [htriangle, pick_volume_vadd, pick_invariant_vadd]
  exact pick_origin_triangle_doubled (q - p) (r - p) h

private theorem pick_polygon_doubled (vertices : Finset (Fin 2 → ℤ))
    (hfull : (interior (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
    2 * (volume (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ))))).toReal =
      pickInvariant (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ)))) := by
  classical
  induction vertices using Finset.strongInductionOn with
  | _ vertices ih =>
    let X := pickCast '' (vertices : Set (Fin 2 → ℤ))
    let P := convexHull ℝ X
    let E := vertices.filter fun z ↦ pickCast z ∈ P.extremePoints ℝ
    have hXfin : X.Finite := vertices.finite_toSet.image pickCast
    have hPconv : Convex ℝ P := convex_convexHull ℝ X
    have hPcomp : IsCompact P := hXfin.isCompact_convexHull ℝ
    have hEP : pickCast '' (E : Set (Fin 2 → ℤ)) = P.extremePoints ℝ := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Finset.mem_filter.mp hz).2
      · intro hx
        rcases extremePoints_convexHull_subset hx with ⟨z, hz, rfl⟩
        exact ⟨z, Finset.mem_filter.mpr ⟨hz, hx⟩, rfl⟩
    have hPhull : convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) = P := by
      calc
        convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) =
            closure (convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ)))) :=
          ((E.finite_toSet.image pickCast).isCompact_convexHull ℝ).isClosed.closure_eq.symm
        _ = P := by
          rw [hEP]
          exact closure_convexHull_extremePoints hPcomp hPconv
    have hspan : affineSpan ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) = ⊤ := by
      apply affineSpan_eq_top_of_nonempty_interior
      rw [hPhull]
      exact hfull
    by_cases hsmall : E.card ≤ 3
    · have hlarge : 3 ≤ E.card := by
        by_contra h
        have hcard : E.card ≤ 2 := by omega
        have hnotop := affineSpan_image_ne_top_of_encard_le_finrank ℝ E.finite_toSet
          (p := pickCast) (by
            rw [Set.encard_coe_eq_coe_finsetCard, Module.finrank_fin_fun]
            exact_mod_cast hcard)
        exact hnotop hspan
      have hcard : E.card = 3 := by omega
      obtain ⟨e : Fin 3 ↪ (Fin 2 → ℤ), he⟩ :=
        Function.Embedding.exists_of_card_eq_finset (s := E) (α := Fin 3)
          (by simpa using hcard.symm)
      have herange : Set.range e = (E : Set (Fin 2 → ℤ)) := by
        have hcoe := congrArg (fun s : Finset (Fin 2 → ℤ) ↦ (s : Set (Fin 2 → ℤ))) he
        simpa using hcoe
      let p := e 0
      let q := e 1
      let r := e 2
      have htriple : pickCast '' (E : Set (Fin 2 → ℤ)) =
          ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [← herange] at hz
          rcases hz with ⟨i, rfl⟩
          fin_cases i <;> simp [p, q, r]
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rintro (rfl | rfl | rfl)
          · exact ⟨p, herange ▸ Set.mem_range_self 0, rfl⟩
          · exact ⟨q, herange ▸ Set.mem_range_self 1, rfl⟩
          · exact ⟨r, herange ▸ Set.mem_range_self 2, rfl⟩
      have hpq : pickCast p ≠ pickCast q := by
        intro hpq
        have hzeroone : (0 : Fin 3) = 1 := e.injective (pick_cast_injective hpq)
        norm_num at hzeroone
      have hdet : pickDet (q - p) (r - p) ≠ 0 := by
        intro hdet
        have hrline : pickCast r ∈ line[ℝ, pickCast p, pickCast q] := by
          apply (pick_side_eq_zero_iff_mem_line hpq (pickCast r)).1
          rw [pick_side_apply]
          norm_num [pickDet, pickCast] at hdet ⊢
          exact_mod_cast hdet
        have hle : affineSpan ℝ
            ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) ≤
              line[ℝ, pickCast p, pickCast q] := by
          apply affineSpan_le.2
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact left_mem_affineSpan_pair ℝ _ _
          · exact right_mem_affineSpan_pair ℝ _ _
          · exact hrline
        rw [← htriple, hspan] at hle
        exact pick_line_ne_top hpq (top_unique hle)
      change 2 * (volume P).toReal = pickInvariant P
      rw [← hPhull, htriple]
      exact pick_triangle_doubled p q r hdet
    · have hEcard : 4 ≤ E.card := by omega
      obtain ⟨e : Fin 4 ↪ (Fin 2 → ℤ), he⟩ :=
        Function.Embedding.exists_of_card_le_finset (s := E) (α := Fin 4)
          (by simpa using hEcard)
      let g : Fin 4 → (Fin 2 → ℝ) := fun i ↦ pickCast (e i)
      have hge (i : Fin 4) : g i ∈ P.extremePoints ℝ := by
        have hei := he (Set.mem_range_self i)
        change e i ∈ vertices.filter (fun z ↦ pickCast z ∈ P.extremePoints ℝ) at hei
        change pickCast (e i) ∈ P.extremePoints ℝ
        exact (Finset.mem_filter.mp hei).2
      let ee : Fin 4 ↪ P.extremePoints ℝ :=
        ⟨fun i ↦ ⟨g i, hge i⟩, fun i j hij ↦ e.injective
          (pick_cast_injective (Subtype.ext_iff.mp hij))⟩
      have hgconv : ConvexIndependent ℝ g := by
        intro s i hi
        by_contra his
        have hiext := (hPconv.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).mp (hge i)
        apply hiext.2
        apply convexHull_mono _ hi
        rintro _ ⟨j, hjs, rfl⟩
        refine ⟨(hge j).1, ?_⟩
        rw [Set.mem_singleton_iff]
        intro hji
        have : j = i := e.injective (pick_cast_injective hji)
        exact his (this ▸ hjs)
      have hgdep : ¬AffineIndependent ℝ g := by
        apply (finrank_vectorSpan_le_iff_not_affineIndependent ℝ g (n := 2) (by simp)).1
        simpa [Module.finrank_fin_fun] using (vectorSpan ℝ (Set.range g)).finrank_le
      obtain ⟨I, y, hyI, hyIc⟩ := Convex.radon_partition hgdep
      have hparts := pick_radon_parts_two hgconv ⟨y, hyI, hyIc⟩
      obtain ⟨i₀, i₁, hi₀i₁, hI⟩ := Set.ncard_eq_two.mp hparts.1
      obtain ⟨j₀, j₁, hj₀j₁, hIc⟩ := Set.ncard_eq_two.mp hparts.2
      have hi₀ : i₀ ∈ I := by simp [hI]
      have hi₁ : i₁ ∈ I := by simp [hI]
      have hj₀ : j₀ ∈ Iᶜ := by simp [hIc]
      have hj₁ : j₁ ∈ Iᶜ := by simp [hIc]
      have hyac : y ∈ openSegment ℝ (g i₀) (g i₁) := by
        apply mem_openSegment_of_ne_left_right
        · intro hiy
          exact ((hgconv.mem_convexHull_iff Iᶜ i₀).mp (by simpa [hiy] using hyIc)) hi₀
        · intro hiy
          exact ((hgconv.mem_convexHull_iff Iᶜ i₁).mp (by simpa [hiy] using hyIc)) hi₁
        · rw [← convexHull_pair, ← Set.image_pair, ← hI]
          exact hyI
      have hybd : y ∈ openSegment ℝ (g j₀) (g j₁) := by
        apply mem_openSegment_of_ne_left_right
        · intro hjy
          exact hj₀ ((hgconv.mem_convexHull_iff I j₀).mp (by simpa [hjy] using hyI))
        · intro hjy
          exact hj₁ ((hgconv.mem_convexHull_iff I j₁).mp (by simpa [hjy] using hyI))
        · rw [← convexHull_pair, ← Set.image_pair, ← hIc]
          exact hyIc
      have hj₀i₀ : j₀ ≠ i₀ := fun h ↦ hj₀ (h ▸ hi₀)
      have hj₀i₁ : j₀ ≠ i₁ := fun h ↦ hj₀ (h ▸ hi₁)
      have hbline : g j₀ ∉ line[ℝ, g i₀, g i₁] := by
        intro hbline
        exact pick_not_collinear_of_convexIndependent hgconv hj₀i₀ hi₀i₁ hj₀i₁
          (collinear_insert_of_mem_affineSpan_pair hbline)
      have hprod : pickSide (g i₀) (g i₁) (g j₀) *
          pickSide (g i₀) (g i₁) (g j₁) < 0 :=
        pick_side_mul_side_neg_of_cross (fun h ↦ hi₀i₁ (e.injective
          (pick_cast_injective h))) hyac hybd hbline
      have hAV : e i₀ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self i₀))).1
      have hCV : e i₁ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self i₁))).1
      have hj₀V : e j₀ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self j₀))).1
      have hj₁V : e j₁ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self j₁))).1
      have finish (B D : Fin 2 → ℤ) (hBV : B ∈ vertices) (hDV : D ∈ vertices)
          (hBpos : 0 < pickSide (g i₀) (g i₁) (pickCast B))
          (hDneg : pickSide (g i₀) (g i₁) (pickCast D) < 0)
          (hyBD : y ∈ openSegment ℝ (pickCast B) (pickCast D)) :
          2 * (volume P).toReal = pickInvariant P := by
        let Vp := vertices.filter fun z ↦ pickCast z ∈ pickHalfPlus (g i₀) (g i₁)
        let Vm := vertices.filter fun z ↦ pickCast z ∈ pickHalfMinus (g i₀) (g i₁)
        have hVp_lt : Vp ⊂ vertices := by
          rw [Finset.filter_ssubset]
          exact ⟨D, hDV, by rw [pick_mem_halfPlus_iff]; linarith⟩
        have hVm_lt : Vm ⊂ vertices := by
          rw [Finset.filter_ssubset]
          exact ⟨B, hBV, by rw [pick_mem_halfMinus_iff]; linarith⟩
        have hXp : pickCast '' (Vp : Set (Fin 2 → ℤ)) =
            X ∩ pickHalfPlus (g i₀) (g i₁) := by
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨⟨z, (Finset.mem_filter.mp hz).1, rfl⟩, (Finset.mem_filter.mp hz).2⟩
          · rintro ⟨⟨z, hz, rfl⟩, hzhalf⟩
            exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzhalf⟩, rfl⟩
        have hXm : pickCast '' (Vm : Set (Fin 2 → ℤ)) =
            X ∩ pickHalfMinus (g i₀) (g i₁) := by
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨⟨z, (Finset.mem_filter.mp hz).1, rfl⟩, (Finset.mem_filter.mp hz).2⟩
          · rintro ⟨⟨z, hz, rfl⟩, hzhalf⟩
            exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzhalf⟩, rfl⟩
        have hAC : e i₀ ≠ e i₁ := fun h ↦ hi₀i₁ (e.injective h)
        have hac : g i₀ ≠ g i₁ := fun h ↦ hAC (pick_cast_injective h)
        have ha : g i₀ ∈ P.extremePoints ℝ := hge i₀
        have hc : g i₁ ∈ P.extremePoints ℝ := hge i₁
        have hHullp : convexHull ℝ (pickCast '' (Vp : Set (Fin 2 → ℤ))) =
            P ∩ pickHalfPlus (g i₀) (g i₁) := by
          rw [hXp]
          exact pick_convexHull_inter_halfPlus hXfin hac ha hc
        have hHullm : convexHull ℝ (pickCast '' (Vm : Set (Fin 2 → ℤ))) =
            P ∩ pickHalfMinus (g i₀) (g i₁) := by
          rw [hXm]
          exact pick_convexHull_inter_halfMinus hXfin hac ha hc
        have hBP : pickCast B ∈ P := subset_convexHull ℝ X ⟨B, hBV, rfl⟩
        have hDP : pickCast D ∈ P := subset_convexHull ℝ X ⟨D, hDV, rfl⟩
        have hfullp : (interior (convexHull ℝ
            (pickCast '' (Vp : Set (Fin 2 → ℤ))))).Nonempty := by
          rw [hHullp]
          exact pick_interior_inter_halfPlus_nonempty hPconv hPcomp.isClosed hfull hac hBP hBpos
        have hfullm : (interior (convexHull ℝ
            (pickCast '' (Vm : Set (Fin 2 → ℤ))))).Nonempty := by
          rw [hHullm]
          exact pick_interior_inter_halfMinus_nonempty hPconv hPcomp.isClosed hfull hac hDP hDneg
        have hpickp := ih Vp hVp_lt hfullp
        have hpickm := ih Vm hVm_lt hfullm
        rw [hHullp] at hpickp
        rw [hHullm] at hpickm
        have hvol := pick_volume_cut hPconv hPcomp hac ha hc
        have hBline : pickCast B ∉ line[ℝ, g i₀, g i₁] := by
          intro hline
          have := (pick_side_eq_zero_iff_mem_line hac (pickCast B)).2 hline
          linarith
        have hinv := pick_invariant_cut hPconv hPcomp hfull hAC ha hBP hc hDP hyac hyBD hBline
        linarith
      rcases mul_neg_iff.mp hprod with ⟨hj₀pos, hj₁neg⟩ | ⟨hj₀neg, hj₁pos⟩
      · exact finish (e j₀) (e j₁) hj₀V hj₁V hj₀pos hj₁neg hybd
      · exact finish (e j₁) (e j₀) hj₁V hj₀V hj₁pos hj₀neg
          (by simpa [openSegment_symm ℝ] using hybd)

/-- Pick's area formula for convex standard-lattice polygons:
`area = I + B / 2 - 1`, where `I` counts interior lattice points and `B`
counts boundary lattice points. The polygon is the full-dimensional convex
hull of finitely many integer-coordinate vertices (`hfull` rules out
degenerate cases); `B` counts integer points on the frontier of the hull.

Sources: Eugen J. Ionascu, "A Parametrization of Equilateral Triangles
Having Integer Coordinates", Journal of Integer Sequences 10 (2007),
Article 07.6.7, standard formula `Area = #b / 2 + #i - 1`, lines 87–100,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Ionascu/ionascu2.tex>;
Kevin A. Broughan, "The gcd-sum function", Journal of Integer Sequences 4
(2001), Article 01.2.2, trapezium application, lines 699–715 (the prose
there prints "+1" but the paper's own derived formula, equation label `10`,
uses the minus-one form),
<https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex>;
Gil Alon and Pete L. Clark, "On the Number of Representations of an
Integer by a Linear Form", Journal of Integer Sequences 8 (2005),
Article 05.5.2, generalized lattice version
`A(P) = δ * (h + b / 2 - 1)`, lines 633–638 (this module is the `δ = 1`
standard-lattice case),
<https://cs.uwaterloo.ca/journals/JIS/VOL8/Clark/clark80.tex>.

Proves `Wanted` entry `pick_convex_lattice_polygon`.

Proof: The triangle case counts lattice points in a half-open fundamental
parallelogram. A crossing diagonal then cuts larger polygons into two smaller
full-dimensional lattice polygons, allowing strong induction on the vertex set.
-/
theorem pick_convex_lattice_polygon (vertices : Finset (Fin 2 → ℤ))
    (hfull :
      (interior
        (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
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
  let P := convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ)))
  have hPcomp : IsCompact P :=
    (vertices.finite_toSet.image pickCast).isCompact_convexHull ℝ
  have hdoubled := pick_polygon_doubled vertices hfull
  change 2 * (volume P).toReal = pickInvariant P at hdoubled
  rw [pickInvariant] at hdoubled
  have hLB := pick_lattice_ncard_eq_interior_add_frontier hPcomp
  have hLBR := congrArg (fun n : ℕ ↦ (n : ℝ)) hLB
  push_cast at hLBR
  change (volume P).toReal =
    (pickLatticePoints (interior P)).ncard +
      (pickLatticePoints (frontier P)).ncard / 2 - 1
  linarith

end MetaMathlibExt
