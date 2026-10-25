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
import Def.Geometry.Convex.PickTheorem.Part12
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

@[simp]
theorem pick_quotientToFundamental_mk (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickQuotientToFundamental u v h (QuotientAddGroup.mk z) =
      ⟨pickFractInt u v z h, pick_fractInt_mem_fundamentalDomain u v z h⟩ := rfl

theorem pick_quotient_fractInt_eq (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (QuotientAddGroup.mk (pickFractInt u v z h) : (Fin 2 → ℤ) ⧸ pickSublattice u v) =
      QuotientAddGroup.mk z := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  have hm : pickIntMap u v (pickFloorCoeffs u v z h) ∈ pickSublattice u v :=
    ⟨pickFloorCoeffs u v z h, rfl⟩
  convert (pickSublattice u v).neg_mem hm using 1
  simp [pickFractInt]

theorem pick_fractInt_eq_self_of_mem (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (hz : pickCast z ∈ ZSpan.fundamentalDomain (pickBasis u v h)) :
    pickFractInt u v z h = z := by
  apply pick_cast_injective
  rw [pick_cast_fractInt]
  exact ZSpan.fract_eq_self.mpr hz

theorem pick_quotientToFundamental_bijective (u v : Fin 2 → ℤ)
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

end MetaMathlibExt
