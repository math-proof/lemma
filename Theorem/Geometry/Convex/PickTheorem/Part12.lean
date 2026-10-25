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
import Def.Geometry.Convex.PickTheorem.Part11
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_repr_cast_fractInt (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
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

theorem pick_fractInt_mem_fundamentalDomain (u v z : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickCast (pickFractInt u v z h) ∈ ZSpan.fundamentalDomain (pickBasis u v h) := by
  rw [ZSpan.mem_fundamentalDomain]
  intro i
  rw [pick_repr_cast_fractInt]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem pick_cast_fractInt (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickCast (pickFractInt u v z h) = ZSpan.fract (pickBasis u v h) (pickCast z) := by
  apply (pickBasis u v h).ext_elem
  intro i
  rw [pick_repr_cast_fractInt, ZSpan.repr_fract_apply]

theorem pick_cast_intMap_mem_zspan (u v c : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickCast (pickIntMap u v c) ∈ Submodule.span ℤ (Set.range (pickBasis u v h)) := by
  rw [(pickBasis u v h).mem_span_iff_repr_mem ℤ]
  intro i
  exact ⟨c i, (pick_repr_cast_intMap u v c h i).symm⟩

theorem pick_fractInt_eq_of_rel (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
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

end MetaMathlibExt
