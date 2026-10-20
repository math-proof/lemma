/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.QuotientToRayClass
import Mathlib.Algebra.Exact.Basic

/-!
# Ray-class-to-ordinary-class-group projection (N406 E4)

Exactness stage of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the ideal-class map on coprime fractional ideals, its descent to the ray
class group, representative rules, the kernel, and exactness at the ray
class group in raw quotient and residue-sign forms.

Source (immutable, ATLAS NumberTheoryI N406 at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`):
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, E4 lines 1120--1132
(`exactSeq_map4`) and 1343--1429 (`exactSeq_exact_at_ray_class`).

Source-to-API map:
- ATLAS `exactSeq_map4`, lines 1120--1132, to `coprimeIdealClassMap` and
  `rayClassToClassGroup` (`QuotientGroup.lift` of `ClassGroup.mk K` after the
  subgroup inclusion);
- ATLAS `exactSeq_exact_at_ray_class`, lines 1343--1429, to
  `rayClassToClassGroup_ker` and
  `rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup`.
- Representation differences: ATLAS works with `FracIdealsCoprime_subgroup`,
  `RayGroup`, and `RayClassGroup` over explicitly coprime subtypes; here these
  are `coprimeFractionalIdeals m`, `rayGroup m`, and `RayClassGroup m`.
  ATLAS lift well-definedness (lines 1124--1132) is discharged via the merged
  E2 lemma `rayGroup_eq_map_rayOneElements` plus `principalRayIdealMap_apply`;
  principal-ideal computations use `principalRayIdealMap_apply`.
  ATLAS reverse exactness (lines 1373--1429) chooses a coprime representative
  via `rayClassMap_surjective`, obtains a principal generator via
  `ClassGroup.mk_eq_one_iff` and `FractionalIdeal.isPrincipal_iff`, proves
  `a ≠ 0`, forms `Units.mk0 a`, and lands in `rayElements m` through the
  definitional `mem_rayElements_iff` comap criterion; the source's valuation
  reconstruction (the analogue of lines 1206--1247) is obsolete and not ported.
- The transported `residueSignToRayClassGroup` corollary has no ATLAS source
  span; it crosses `rayElementsQuotientEquivResidueSign` using E3's
  transported map and its range.

E4 partial-stage boundary: this module stops before projection surjectivity
(source lines 1431--1480, E5, which needs coprime ideal-class representatives)
and before the final six-term wrapper (E5). It does not reimplement E1--E3.
-/

@[expose] noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Ideal-class map on coprime fractional ideals: `ClassGroup.mk K` after the
subgroup inclusion (ATLAS `exactSeq_map4` before the quotient lift). -/
noncomputable def coprimeIdealClassMap (m : Modulus K) :
    coprimeFractionalIdeals m →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (coprimeFractionalIdeals m).subtype

/-- Pointwise evaluation of the coprime ideal-class map. -/
@[simp] theorem coprimeIdealClassMap_apply (m : Modulus K)
    (I : coprimeFractionalIdeals m) :
    coprimeIdealClassMap m I =
      ClassGroup.mk K ((coprimeFractionalIdeals m).subtype I) :=
  rfl

/-- The ray group lies in the kernel of the ideal-class map. -/
theorem rayGroup_le_coprimeIdealClassMap_ker (m : Modulus K) :
    rayGroup m ≤ (coprimeIdealClassMap m).ker := by
  rw [rayGroup_eq_map_rayOneElements]
  intro y hy
  obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp hy
  rw [MonoidHom.mem_ker, coprimeIdealClassMap_apply, ClassGroup.mk_eq_one_iff,
    FractionalIdeal.isPrincipal_iff]
  refine ⟨((x : Kˣ) : K), ?_⟩
  have h := principalRayIdealMap_apply m x
  have hval : (((principalRayIdealMap m x :
      coprimeFractionalIdeals m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K) := by
    rw [h, coe_toPrincipalIdeal]
  simpa only [Subgroup.coe_subtype] using hval

/-- Projection from the ray class group to the ordinary class group
(ATLAS `exactSeq_map4`). -/
noncomputable def rayClassToClassGroup (m : Modulus K) :
    RayClassGroup m →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (rayGroup m) (coprimeIdealClassMap m)
    (rayGroup_le_coprimeIdealClassMap_ker m)

/-- The projection evaluated on a class representative. -/
@[simp] theorem rayClassToClassGroup_rayClassMap (m : Modulus K)
    (I : coprimeFractionalIdeals m) :
    rayClassToClassGroup m (rayClassMap m I) = coprimeIdealClassMap m I := by
  simp [rayClassToClassGroup, rayClassMap]

/-- The projection undoes the class map as homomorphisms. -/
theorem rayClassToClassGroup_comp_rayClassMap (m : Modulus K) :
    (rayClassToClassGroup m).comp (rayClassMap m) = coprimeIdealClassMap m := by
  ext I
  simp only [MonoidHom.comp_apply]
  exact rayClassToClassGroup_rayClassMap m I

/-- Composition of the projection with the quotient map on generators. -/
theorem rayClassToClassGroup_rayQuotientToRayClassGroup (m : Modulus K)
    (x : rayElements m) :
    rayClassToClassGroup m (rayQuotientToRayClassGroup m (QuotientGroup.mk x)) =
      coprimeIdealClassMap m (principalRayIdealMap m x) := by
  rw [rayQuotientToRayClassGroup_mk, rayElementClassMap_apply,
    ← rayClassToClassGroup_rayClassMap]

/-- Composition of the projection with the transported residue-sign map. -/
theorem rayClassToClassGroup_residueSignToRayClassGroup (m : Modulus K)
    (x : rayElements m) :
    rayClassToClassGroup m
        (residueSignToRayClassGroup m (residueSignMap m x)) =
      coprimeIdealClassMap m (principalRayIdealMap m x) := by
  rw [residueSignToRayClassGroup_residueSignMap,
    rayElementClassMap_apply, ← rayClassToClassGroup_rayClassMap]

/-- Exactness at the ray class group: the kernel of the projection is the
range of the quotient map (ATLAS `exactSeq_exact_at_ray_class`). -/
theorem rayClassToClassGroup_ker (m : Modulus K) :
    (rayClassToClassGroup m).ker =
      MonoidHom.range (rayQuotientToRayClassGroup m) := by
  apply le_antisymm
  · intro c hc
    rw [MonoidHom.mem_ker] at hc
    obtain ⟨I, rfl⟩ := rayClassMap_surjective m c
    rw [rayClassToClassGroup_rayClassMap] at hc
    have hunfold : ClassGroup.mk K
        ((coprimeFractionalIdeals m).subtype I) = 1 := hc
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at hunfold
    obtain ⟨a, ha⟩ := hunfold
    have ha_val : ((((coprimeFractionalIdeals m).subtype I :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ a := ha
    have ha_val' : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
      simpa only [Subgroup.coe_subtype] using ha_val
    have ha_ne : a ≠ 0 := by
      intro ha_zero
      rw [ha_zero, FractionalIdeal.spanSingleton_zero] at ha_val'
      exact Units.ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ha_val'
    set α : Kˣ := Units.mk0 a ha_ne with hα
    have hI_eq_topi : (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        toPrincipalIdeal (𝓞 K) K α := by
      apply Units.ext
      show ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = _
      rw [coe_toPrincipalIdeal, hα, Units.val_mk0]
      exact ha_val'
    have hα_coprime : α ∈ rayElements m := by
      rw [mem_rayElements_iff, ← hI_eq_topi]
      exact I.property
    set γ : rayElements m := ⟨α, hα_coprime⟩ with hγ
    have hγ_eq : principalRayIdealMap m γ = I := by
      apply Subtype.ext
      have h := principalRayIdealMap_apply m γ
      rw [h, hI_eq_topi]
    refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk γ, ?_⟩
    rw [rayQuotientToRayClassGroup_mk, rayElementClassMap_apply, hγ_eq]
  · intro c hc
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hc
    rw [MonoidHom.mem_ker]
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (rayOneElements m) q
    rw [QuotientGroup.mk'_apply, rayQuotientToRayClassGroup_mk,
      rayElementClassMap_apply, rayClassToClassGroup_rayClassMap]
    rw [coprimeIdealClassMap_apply, ClassGroup.mk_eq_one_iff,
      FractionalIdeal.isPrincipal_iff]
    refine ⟨((x : Kˣ) : K), ?_⟩
    have h := principalRayIdealMap_apply m x
    have hval : (((principalRayIdealMap m x :
        coprimeFractionalIdeals m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K) := by
      rw [h, coe_toPrincipalIdeal]
    simpa only [Subgroup.coe_subtype] using hval

/-- Exactness at the ray class group as `MulExact`, raw quotient form
(ATLAS `exactSeq_exact_at_ray_class`). -/
theorem rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup
    (m : Modulus K) :
    Function.MulExact (rayQuotientToRayClassGroup m)
      (rayClassToClassGroup m) := by
  rw [MonoidHom.mulExact_iff, rayClassToClassGroup_ker]

/-- Exactness at the ray class group as `MulExact`, residue-sign form. -/
theorem residueSignToRayClassGroup_mulExact_rayClassToClassGroup
    (m : Modulus K) :
    Function.MulExact (residueSignToRayClassGroup m)
      (rayClassToClassGroup m) := by
  rw [MonoidHom.mulExact_iff]
  have hrange : MonoidHom.range (residueSignToRayClassGroup m) =
      MonoidHom.range (rayQuotientToRayClassGroup m) := by
    unfold residueSignToRayClassGroup
    rw [MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe,
      MulEquiv.range_eq_top, ← MonoidHom.range_eq_map]
  rw [hrange, ← rayClassToClassGroup_ker]

end Modulus
end NumberField
