/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Extended.lean -/

import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# Localization commutes with fractional-ideal division

This module adds the missing commutation of localization with the
fractional-ideal colon/division operation for a finitely generated
denominator, plus the Noetherian corollary.

Mathlib already provides `FractionalIdeal.extended`, `extended_add`,
`extended_mul`, and `extendedHom`; those wrappers are not duplicated here.

## Source correspondence

The source is Andrew V. Sutherland, *18.785 Number Theory I*, Lecture 3,
[Lemma 3.1](https://math.mit.edu/classes/18.785/2021fa/LectureNotes3.pdf#page=1).
In its notation, localization sends fractional ideals `I` and `J` to `Iₚ` and `Jₚ`,
and the last displayed identity is `(I : J)ₚ = (Iₚ : Jₚ)`, where
`(I : J) = {x ∈ K | xJ ⊆ I}`.  Mathlib writes this colon operation as `/`.

The correspondence with the declarations below is as follows.

* `Submodule.localized'_div_of_fg` proves the displayed colon identity directly.  It
  replaces the source's Noetherian assumption by the precise hypothesis used to clear a
  common denominator, namely that `J` is finitely generated.  It also works for commutative
  rings and any localized ambient module, so this is slightly more general than the source.
* `coe_extendedHom_eq_localized'` identifies Mathlib's fractional-ideal extension map with
  `Submodule.localized'` on underlying submodules.
* `FractionalIdeal.extendedHom_div_of_fg` transports the first result across that
  identification.  Its `J ≠ 0` assumption is the side condition required by Mathlib's
  coercion theorem for fractional-ideal division.
* `FractionalIdeal.extendedHom_div` derives finite generation from `IsNoetherianRing A` and
  is the direct Lean counterpart of the source lemma.  Taking the multiplicative set to be
  the complement of a prime gives the source's `Aₚ` statement; leaving it arbitrary matches
  the source's final sentence, which explicitly allows any multiplicative subset.
-/

namespace Submodule

variable {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]
variable [Algebra R S] [Algebra R K] [Algebra S K]
variable [IsScalarTower R S K]
variable {p : Submonoid R} [IsLocalization p S]
variable [IsLocalizedModule p (.id : K →ₗ[R] K)]

/-- Localization commutes with submodule division for a finitely generated
denominator. -/
lemma localized'_div_of_fg (I J : Submodule R K) (hJ : J.FG) :
    (I / J).localized' S p (.id : K →ₗ[R] K) =
      I.localized' S p (.id : K →ₗ[R] K) /
        J.localized' S p (.id : K →ₗ[R] K) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [mem_div_iff_forall_mul_mem]
    rintro y hy
    rw [mem_localized'] at hx hy ⊢
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine ⟨a * b, (mem_div_iff_forall_mul_mem.mp ha) b hb, s * t, ?_⟩
    exact (IsLocalizedModule.mk'_mul_mk'_of_map_mul (.id : K →ₗ[R] K)
      (fun _ _ => rfl) a b s t).symm
  · intro x hx
    rw [mem_div_iff_forall_mul_mem] at hx
    obtain ⟨t, htspan⟩ := hJ
    have hden (j : t) : ∃ s : p, (s : R) • (x * (j : K)) ∈ I := by
      have hj : (j : K) ∈ J := by
        rw [← htspan]
        exact Submodule.subset_span j.property
      have hjloc : (j : K) ∈ J.localized' S p (.id : K →ₗ[R] K) := by
        rw [mem_localized']
        exact ⟨j, hj, 1, by simp⟩
      obtain ⟨a, ha, s, hs⟩ := (mem_localized' S p (.id : K →ₗ[R] K) I _).mp
        (hx (j : K) hjloc)
      refine ⟨s, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff] at hs
      simpa only [LinearMap.id_apply] using hs ▸ ha
    choose d hd using hden
    let D : p := ∏ j : t, d j
    have hgen : (↑t : Set K) ⊆ I.comap (LinearMap.mulLeft R ((D : R) • x)) := by
      intro j hj
      let j' : t := ⟨j, hj⟩
      change ((D : R) • x) * j ∈ I
      rw [Algebra.smul_mul_assoc]
      have hprod : D = (Finset.univ.erase j').prod d * d j' := by
        change (Finset.univ.prod d : p) = _
        exact (Finset.prod_erase_mul Finset.univ d (Finset.mem_univ j')).symm
      rw [hprod, Submonoid.coe_mul, mul_smul]
      exact I.smul_mem _ (hd j')
    have hsub : J ≤ I.comap (LinearMap.mulLeft R ((D : R) • x)) := by
      rw [← htspan]
      exact Submodule.span_le.mpr hgen
    rw [mem_localized']
    refine ⟨(D : R) • x, ?_, D, ?_⟩
    · rw [mem_div_iff_forall_mul_mem]
      intro y hy
      exact hsub hy
    · rw [IsLocalizedModule.mk'_eq_iff]
      rfl

end Submodule

namespace FractionalIdeal
open nonZeroDivisors
variable {A B K : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
variable [Field K] [Algebra A B] [Module.IsTorsionFree A B]
variable [Algebra A K] [Algebra B K] [IsScalarTower A B K]
variable [IsFractionRing A K] [IsFractionRing B K]

/-- The coercion of `extendedHom` agrees with `Submodule.localized'`. -/
lemma coe_extendedHom_eq_localized' (S : Submonoid A) [IsLocalization S B]
    [IsLocalizedModule S (.id : K →ₗ[A] K)] (I : FractionalIdeal A⁰ K) :
    ((extendedHom K B I : FractionalIdeal B⁰ K) : Submodule B K) =
      (I : Submodule A K).localized' B S (.id : K →ₗ[A] K) := by
  change ((I.extended K _ : FractionalIdeal B⁰ K) : Submodule B K) = _
  rw [coe_extended_eq_span, Submodule.localized'_eq_span]
  have hmap : IsLocalization.map K (algebraMap A B)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective A B)) = RingHom.id K := by
    apply IsLocalization.ringHom_ext A⁰
    ext a
    simp only [RingHom.comp_apply, IsLocalization.map_eq, RingHom.id_apply]
    exact (IsScalarTower.algebraMap_apply A B K a).symm
  rw [hmap]
  rfl

/-- Extension commutes with division for a nonzero finitely generated denominator. -/
theorem extendedHom_div_of_fg (S : Submonoid A) [IsLocalization S B]
    (I J : FractionalIdeal A⁰ K) (hJ0 : J ≠ 0) (hJ : (J : Submodule A K).FG) :
    extendedHom K B (I / J) = extendedHom K B I / extendedHom K B J := by
  let _ : IsLocalizedModule S (.id : K →ₗ[A] K) := isLocalizedModule_id S K B
  have heJ0 : extendedHom K B J ≠ 0 :=
    (extendedHom_eq_zero_iff K B).not.mpr hJ0
  apply coeToSubmodule_injective
  change ((extendedHom K B (I / J) : FractionalIdeal B⁰ K) : Submodule B K) =
    ((extendedHom K B I / extendedHom K B J : FractionalIdeal B⁰ K) : Submodule B K)
  rw [coe_div heJ0]
  calc
    ((extendedHom K B (I / J) : FractionalIdeal B⁰ K) : Submodule B K) =
        ((I / J : FractionalIdeal A⁰ K) : Submodule A K).localized' B S
          (.id : K →ₗ[A] K) := coe_extendedHom_eq_localized' S (I / J)
    _ = ((I : Submodule A K) / (J : Submodule A K)).localized' B S
          (.id : K →ₗ[A] K) := by rw [coe_div hJ0]
    _ = (I : Submodule A K).localized' B S (.id : K →ₗ[A] K) /
          (J : Submodule A K).localized' B S (.id : K →ₗ[A] K) :=
      Submodule.localized'_div_of_fg _ _ hJ
    _ = ((extendedHom K B I : FractionalIdeal B⁰ K) : Submodule B K) /
          ((extendedHom K B J : FractionalIdeal B⁰ K) : Submodule B K) := by
      rw [coe_extendedHom_eq_localized' S, coe_extendedHom_eq_localized' S]

/-- Extension commutes with division for a nonzero denominator over a Noetherian base ring. -/
theorem extendedHom_div [IsNoetherianRing A]
    (S : Submonoid A) [IsLocalization S B] (I J : FractionalIdeal A⁰ K) (hJ : J ≠ 0) :
    extendedHom K B (I / J) = extendedHom K B I / extendedHom K B J :=
  extendedHom_div_of_fg S I J hJ (fg_of_isNoetherianRing le_rfl J)
end FractionalIdeal
