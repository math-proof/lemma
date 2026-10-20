/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean -/

import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Group actions on fractional ideals

This module constructs the action of a group of ring automorphisms on fractional
ideals of a fraction ring.
-/

open scoped nonZeroDivisors
open scoped Pointwise

namespace FractionalIdeal

variable (R K : Type*) [CommRing R] [IsDomain R] [CommRing K]
  [Algebra R K] [IsFractionRing R K]

/-- Ring automorphisms of `R` act on fractional ideals via `ringEquivOfRingEquiv`. -/
noncomputable def ringEquivOfRingEquivHom :
    RingAut R →* RingAut (FractionalIdeal R⁰ K) where
  toFun σ := FractionalIdeal.ringEquivOfRingEquiv K K σ
  map_one' := FractionalIdeal.ringEquivOfRingEquiv_refl K
  map_mul' σ τ := FractionalIdeal.ringEquivOfRingEquiv_trans K K K τ σ

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
  [CommRing K] [Algebra R K] [IsFractionRing R K]
  [MulSemiringAction G R]

/-- The `MulSemiringAction` on fractional ideals induced by that on the base ring. -/
noncomputable instance instMulSemiringAction :
    MulSemiringAction G (FractionalIdeal R⁰ K) :=
  MulSemiringAction.compHom _ ((ringEquivOfRingEquivHom R K).comp
    (MulSemiringAction.toRingAut G R))

/-- The induced multiplicative action on the group of invertible fractional ideals.

This is scoped to avoid the instance diamond documented for `Units.mulAction'`. -/
noncomputable abbrev unitsMulDistribMulAction :
    MulDistribMulAction G (FractionalIdeal R⁰ K)ˣ :=
  Units.mulDistribMulActionRight

scoped[FractionalIdealUnits] attribute [instance]
  FractionalIdeal.unitsMulDistribMulAction

open scoped FractionalIdealUnits

/-- The action on invertible fractional ideals agrees with the ambient action. -/
@[simp]
theorem units_smul_val (g : G) (I : (FractionalIdeal R⁰ K)ˣ) :
    ((g • I : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      g • (I : FractionalIdeal R⁰ K) :=
  rfl

/-- The action on a fractional ideal is induced by the corresponding base-ring automorphism. -/
@[simp]
theorem smul_def (g : G) (I : FractionalIdeal R⁰ K) :
    g • I =
      FractionalIdeal.ringEquivOfRingEquiv K K
        (MulSemiringAction.toRingAut G R g) I :=
  rfl

/-- Membership in a translated fractional ideal via a forward witness. -/
theorem mem_smul_iff_exists (g : G) (I : FractionalIdeal R⁰ K) (x : K) :
    x ∈ g • I ↔ ∃ y ∈ I,
      IsFractionRing.ringEquivOfRingEquiv
        (MulSemiringAction.toRingAut G R g) y = x := by
  rw [smul_def]
  change x ∈ (ringEquivOfRingEquiv K K (MulSemiringAction.toRingAut G R g) I).val ↔ _
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply_val, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- Membership in a translated fractional ideal is tested after applying the inverse
fraction-field automorphism. -/
theorem mem_smul_iff (g : G) (I : FractionalIdeal R⁰ K) (x : K) :
    x ∈ g • I ↔
      (IsFractionRing.ringEquivOfRingEquiv
        (MulSemiringAction.toRingAut G R g)).symm x ∈ I := by
  let F := IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
    (MulSemiringAction.toRingAut G R g)
  rw [mem_smul_iff_exists (R := R) (K := K)]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← h, F.symm_apply_apply]
    exact hy
  · intro hx
    exact ⟨F.symm x, hx, F.apply_symm_apply x⟩

/-- The action on an integral ideal agrees with the induced fractional-ideal action. -/
@[simp]
theorem smul_coeIdeal (g : G) (I : Ideal R) :
    g • (I : FractionalIdeal R⁰ K) =
      ((g • I : Ideal R) : FractionalIdeal R⁰ K) := by
  ext x
  simp only [mem_smul_iff_exists, mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hx⟩
    have h : IsFractionRing.ringEquivOfRingEquiv
        (MulSemiringAction.toRingAut G R g) (algebraMap R K a) =
        algebraMap R K (g • a) := by
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      rfl
    refine ⟨g • a, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mpr ?_, ?_⟩
    · simpa using ha
    · rw [← hx, h]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have h : IsFractionRing.ringEquivOfRingEquiv
        (MulSemiringAction.toRingAut G R g) (algebraMap R K (g⁻¹ • b)) =
        algebraMap R K b := by
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      congr 1
      exact smul_inv_smul g b
    exact ⟨_, ⟨_, hb, rfl⟩, h⟩

end FractionalIdeal
