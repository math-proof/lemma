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
import Def.Geometry.Convex.PickTheorem.Part6
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_reflect_cast (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickReflect u v h (pickCast z) = pickCast (u + v - z) := by
  ext i
  simp [pickReflect, pick_basis_apply, pickVecs, pickCast]

theorem pick_mem_reflected_triangle_iff (u v : Fin 2 → ℤ)
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

theorem pick_parallelepiped_eq_union (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
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

end MetaMathlibExt
