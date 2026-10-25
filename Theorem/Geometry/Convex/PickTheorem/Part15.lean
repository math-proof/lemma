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
import Abbrev.Geometry.Convex.PickTheorem.Part2
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_repr_cast_u (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickBasis u v h).repr (pickCast u) = Finsupp.single 0 1 := by
  have hu : pickBasis u v h 0 = pickCast u := by
    simp [pick_basis_apply, pickVecs]
  rw [← hu, Module.Basis.repr_self]

theorem pick_repr_cast_v (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickBasis u v h).repr (pickCast v) = Finsupp.single 1 1 := by
  have hv : pickBasis u v h 1 = pickCast v := by
    simp [pick_basis_apply, pickVecs]
  rw [← hv, Module.Basis.repr_self]

theorem pick_fundamental_inter_triangle (u v : Fin 2 → ℤ)
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

end MetaMathlibExt
