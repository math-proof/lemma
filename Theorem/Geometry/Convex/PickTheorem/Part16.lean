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
import Def.Geometry.Convex.PickTheorem.Part14
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_intReflect_mem_interior_iff (u v z : Fin 2 → ℤ)
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

theorem pick_intReflect_bijOn (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
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

theorem pick_triangle_lattice_count (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
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

theorem pick_triangle_eq_explicit (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
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

end MetaMathlibExt
