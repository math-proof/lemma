/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.IntegralUnits
import sympy.atlas.NumberTheory.NumberField.RayClass.PrincipalIdeal
import sympy.atlas.NumberTheory.NumberField.RayClass.Group
/-!
# Ray-element quotient to the ray class group (N406 E3)

Quotient stage of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the ray-element class map into the ray class group, its descent to the
ray-element quotient, representative rules, kernels, and exactness at the
quotient, plus the transported residue-sign corollary.

Source (immutable, ATLAS NumberTheoryI N406 at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`):
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, E3 lines 1110--1118
(`exactSeq_map3`) and 1284--1342 (`exactSeq_exact_at_quotient`).

Source-to-API map:
- ATLAS `exactSeq_map3`, lines 1110--1118, to `rayElementClassMap` and
  `rayQuotientToRayClassGroup` (`QuotientGroup.lift` of the `rayClassMap` after
  `principalRayIdealMap` composite);
- ATLAS `exactSeq_exact_at_quotient`, lines 1284--1342, to
  `rayQuotientToRayClassGroup_ker` and
  `integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup`.
- Representation differences: ATLAS works with `UnitsCoprime`,
  `UnitsCongruent_in_UnitsCoprime`, and `QuotientUnits`; here these are
  `rayElements m`, `rayOneElements m`, and `rayElements m ⧸ rayOneElements m`.
  ATLAS valuation/subtype reconstruction (lines 1206--1282) is replaced by the
  merged E2 lemmas `rayGroup_eq_map_rayOneElements` and
  `toPrincipalIdeal_eq_iff_exists_integralUnit_mul`; the integral-unit
  principal-ideal computation (lines 1160--1175) is replayed locally as
  `principalRayIdealMap_integralUnitsToRayElements`.
- The transported `residueSignToRayClassGroup` family has no ATLAS source span;
  it is the canonical corollary across `rayElementsQuotientEquivResidueSign`.

E3 partial-stage boundary: this module stops before `exactSeq_map4`
(lines 1120--1132), exactness at the ray class group (lines 1343--1429), and
coprime representatives / surjectivity / the six-term wrapper
(lines 1431--1480). It does not reimplement E1, E2, or the quotient
equivalence. Exactness holds only at the quotient: the kernel of
`rayElementClassMap` itself can be larger than `rayOneElements` (it need not
equal `rayOneElements`: it also contains the images of integral units, which
need not lie in `rayOneElements`), so no such kernel equality is claimed.
-/

@[expose] noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Ray-element class map: principal ideal followed by the class projection
(ATLAS `exactSeq_map3` before the quotient lift). -/
noncomputable def rayElementClassMap (m : Modulus K) :
    rayElements m →* RayClassGroup m :=
  (rayClassMap m).comp (principalRayIdealMap m)

/-- Pointwise evaluation of the ray-element class map. -/
@[simp] theorem rayElementClassMap_apply (m : Modulus K) (x : rayElements m) :
    rayElementClassMap m x = rayClassMap m (principalRayIdealMap m x) :=
  rfl

/-- Ray-one elements lie in the kernel of the ray-element class map. -/
theorem rayOneElements_le_rayElementClassMap_ker (m : Modulus K) :
    rayOneElements m ≤ (rayElementClassMap m).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, rayElementClassMap_apply, rayClassMap_eq_one_iff]
  rw [rayGroup_eq_map_rayOneElements]
  exact Subgroup.mem_map_of_mem _ hx

/-- Quotient-to-ray-class map (ATLAS `exactSeq_map3`). -/
noncomputable def rayQuotientToRayClassGroup (m : Modulus K) :
    (rayElements m ⧸ rayOneElements m) →* RayClassGroup m :=
  QuotientGroup.lift (rayOneElements m) (rayElementClassMap m)
    (rayOneElements_le_rayElementClassMap_ker m)

/-- The quotient map evaluated on a class representative. -/
@[simp] theorem rayQuotientToRayClassGroup_mk (m : Modulus K)
    (x : rayElements m) :
    rayQuotientToRayClassGroup m (QuotientGroup.mk x) =
      rayElementClassMap m x := by
  simp [rayQuotientToRayClassGroup]

/-- An embedded integral unit generates the unit principal ideal, hence maps
to one (forward exactness input; ATLAS lines 1160--1175). -/
theorem principalRayIdealMap_integralUnitsToRayElements (m : Modulus K)
    (u : (𝓞 K)ˣ) :
    principalRayIdealMap m (integralUnitsToRayElements m u) = 1 := by
  apply Subtype.ext
  rw [principalRayIdealMap_apply]
  have h : toPrincipalIdeal (𝓞 K) K
      ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
      toPrincipalIdeal (𝓞 K) K 1 := by
    rw [toPrincipalIdeal_eq_iff_exists_integralUnit_mul]
    exact ⟨u, by simp [integralUnitsToRayElements_coe,
      integralUnitsToFieldUnits]⟩
  simpa using h

/-- Exactness at the quotient: the kernel of the quotient-to-ray-class map is
the range of the integral-unit quotient map
(ATLAS `exactSeq_exact_at_quotient`). -/
theorem rayQuotientToRayClassGroup_ker (m : Modulus K) :
    (rayQuotientToRayClassGroup m).ker =
      MonoidHom.range (integralUnitsToRayQuotient m) := by
  apply le_antisymm
  · intro q hq
    rw [MonoidHom.mem_ker] at hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (rayOneElements m) q
    rw [QuotientGroup.mk'_apply, rayQuotientToRayClassGroup_mk,
      rayElementClassMap_apply, rayClassMap_eq_one_iff] at hq
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp
      ((rayGroup_eq_map_rayOneElements m).symm ▸ hq)
    have htop : toPrincipalIdeal (𝓞 K) K (x : Kˣ) =
        toPrincipalIdeal (𝓞 K) K (y : Kˣ) := by
      have hcongr := congrArg Subtype.val hxy
      have hx : ((principalRayIdealMap m x : coprimeFractionalIdeals m) :
          (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
          toPrincipalIdeal (𝓞 K) K (x : Kˣ) :=
        principalRayIdealMap_apply m x
      have hy' : ((principalRayIdealMap m y : coprimeFractionalIdeals m) :
          (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
          toPrincipalIdeal (𝓞 K) K (y : Kˣ) :=
        principalRayIdealMap_apply m y
      rw [hx, hy'] at hcongr
      exact hcongr.symm
    obtain ⟨u, hu⟩ :=
      (toPrincipalIdeal_eq_iff_exists_integralUnit_mul (x : Kˣ) (y : Kˣ)).mp htop
    refine MonoidHom.mem_range.mpr ⟨u, ?_⟩
    rw [integralUnitsToRayQuotient_apply]
    symm
    change (x : rayElements m ⧸ rayOneElements m) =
      ((integralUnitsToRayElements m u : rayElements m) :
        rayElements m ⧸ rayOneElements m)
    rw [QuotientGroup.eq_iff_div_mem]
    have hdiv : x / integralUnitsToRayElements m u = y := by
      apply Subtype.ext
      simp only [Subgroup.coe_div, integralUnitsToRayElements_coe,
        integralUnitsToFieldUnits, RingHom.toMonoidHom_eq_coe]
      change (x : Kˣ) / Units.map (algebraMap (𝓞 K) K) u = (y : Kˣ)
      rw [hu, mul_comm]
      exact mul_div_cancel_right _ _
    rwa [hdiv]
  · intro q hq
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hq
    rw [MonoidHom.mem_ker, integralUnitsToRayQuotient_apply,
      rayQuotientToRayClassGroup_mk, rayElementClassMap_apply]
    rw [principalRayIdealMap_integralUnitsToRayElements, map_one]

/-- Exactness at the quotient as `MulExact`
(ATLAS `exactSeq_exact_at_quotient`). -/
theorem integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup
    (m : Modulus K) :
    Function.MulExact (integralUnitsToRayQuotient m)
      (rayQuotientToRayClassGroup m) := by
  rw [MonoidHom.mulExact_iff, rayQuotientToRayClassGroup_ker]

/-- Transported residue-sign-to-ray-class map across the canonical quotient
equivalence. -/
noncomputable def residueSignToRayClassGroup (m : Modulus K) :
    ResidueSignTarget m →* RayClassGroup m :=
  (rayQuotientToRayClassGroup m).comp
    (rayElementsQuotientEquivResidueSign m).symm.toMonoidHom

/-- The transported map undoes the quotient equivalence. -/
@[simp] theorem residueSignToRayClassGroup_equiv (m : Modulus K)
    (q : rayElements m ⧸ rayOneElements m) :
    residueSignToRayClassGroup m (rayElementsQuotientEquivResidueSign m q) =
      rayQuotientToRayClassGroup m q := by
  simp [residueSignToRayClassGroup]

/-- The transported map evaluated on a residue-sign value. -/
theorem residueSignToRayClassGroup_residueSignMap (m : Modulus K)
    (x : rayElements m) :
    residueSignToRayClassGroup m (residueSignMap m x) =
      rayElementClassMap m x := by
  calc residueSignToRayClassGroup m (residueSignMap m x)
      = residueSignToRayClassGroup m
          (rayElementsQuotientEquivResidueSign m (QuotientGroup.mk x)) := by
        rw [rayElementsQuotientEquivResidueSign_mk]
    _ = rayQuotientToRayClassGroup m (QuotientGroup.mk x) :=
        residueSignToRayClassGroup_equiv m _
    _ = rayElementClassMap m x := rayQuotientToRayClassGroup_mk m x

/-- The transport square: precomposing with the residue-sign map recovers the
ray-element class map. -/
theorem residueSignToRayClassGroup_comp_residueSignMap (m : Modulus K) :
    (residueSignToRayClassGroup m).comp (residueSignMap m) =
      rayElementClassMap m := by
  ext x
  simp only [MonoidHom.comp_apply]
  exact residueSignToRayClassGroup_residueSignMap m x

/-- Kernel of the transported map is the range of the residue-sign unit map. -/
theorem residueSignToRayClassGroup_ker (m : Modulus K) :
    (residueSignToRayClassGroup m).ker =
      MonoidHom.range (integralUnitsToResidueSign m) := by
  unfold residueSignToRayClassGroup integralUnitsToResidueSign
  change
    ((rayQuotientToRayClassGroup m).comp
      (rayElementsQuotientEquivResidueSign m).symm).ker =
    ((rayElementsQuotientEquivResidueSign m).toMonoidHom.comp
      (integralUnitsToRayQuotient m)).range
  rw [MonoidHom.ker_comp_mulEquiv, MonoidHom.range_comp,
    rayQuotientToRayClassGroup_ker, MulEquiv.symm_symm,
    MulEquiv.toMonoidHom_eq_coe]

/-- Exactness at the residue-sign target as `MulExact`. -/
theorem integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup
    (m : Modulus K) :
    Function.MulExact (integralUnitsToResidueSign m)
      (residueSignToRayClassGroup m) := by
  rw [MonoidHom.mulExact_iff, residueSignToRayClassGroup_ker]

end Modulus
end NumberField
