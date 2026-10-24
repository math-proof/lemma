/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.ResidueSign
import Lemma.Nat.NumberField.RayClass.ResidueSign
import Mathlib.Algebra.Exact.Basic

/-!
# Integral units into ray elements and exactness at units (N406 E1)

Left endpoint of the six-term exact sequence in ATLAS NumberTheoryI N406,
Theorem 21.8, Section 21.3: the integral-unit embedding, the ray-one unit
subgroup, the quotient and residue-sign endpoint maps, and exactness at units.

Source: `v1/Atlas/NumberTheoryI/code/RayClassFields.lean`,
declarations `exactSeq_map1`, `okUnitsToKUnits`, `valuation_algebraMap_unit_eq_one`,
`okUnitsInUnitsCoprime`, `okUnitsToUnitsCoprime`, `exactSeq_map2` (source lines
1012--1052) and `exactSeq_exact_at_units` (source lines 1134--1158).

Source-to-API map:
- ATLAS `UnitsCoprime` is `rayElements m`; ATLAS `UnitsCongruent_in_UnitsCoprime`
  is `rayOneElements m`; ATLAS `QuotientUnits` is the direct quotient
  `rayElements m ⧸ rayOneElements m`; ATLAS `SignsTimesUnits` is
  `ResidueSignTarget m` via `rayElementsQuotientEquivResidueSign` (PR #1367).
- ATLAS `exactSeq_map1` is `integralRayOneUnitsInclusion m`;
  `okUnitsToKUnits` is `integralUnitsToFieldUnits`;
  `valuation_algebraMap_unit_eq_one` is discharged inline in
  `integralUnitsToRayElements m` by Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem`;
  `okUnitsToUnitsCoprime` is `integralUnitsToRayElements m`;
  `exactSeq_map2` is `integralUnitsToRayQuotient m`.
- ATLAS `exactSeq_exact_at_units` is `integralUnits_mulExact_quotient`;
  `integralUnits_mulExact_residueSign` is the transported residue-sign form used
  by the concrete six-term sequence.

E1 partial-stage boundary: this module stops before the principal-ideal material
at source line 1054 and before the integral-unit/principal-ideal bridge at line
1160. It does not add the map to the ray class group or later exactness stages.
-/

@[expose] noncomputable section

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Integral units embedded into field units (ATLAS `okUnitsToKUnits`). -/
def integralUnitsToFieldUnits : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K).toMonoidHom

/-- Integral units land in ray elements (ATLAS `okUnitsToUnitsCoprime`;
ATLAS `valuation_algebraMap_unit_eq_one` is discharged inline below). -/
def integralUnitsToRayElements (m : Modulus K) :
    (𝓞 K)ˣ →* rayElements m :=
  MonoidHom.codRestrict integralUnitsToFieldUnits (rayElements m)
    (fun u => mem_rayElements_of_valuation_eq_one m
      (integralUnitsToFieldUnits u) (fun v _ =>
        (v.valuation_eq_one_iff_notMem).2 (v.asIdeal.notMem_of_isUnit u.isUnit)))

/-- Coercion of the ray-element image back to field units. -/
@[simp] theorem integralUnitsToRayElements_coe (m : Modulus K) (u : (𝓞 K)ˣ) :
    ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
      integralUnitsToFieldUnits u :=
  rfl

/-- Ray-one integral units, by comap (ATLAS `UnitsInCongruenceSubgroup`). -/
def integralRayOneUnits (m : Modulus K) : Subgroup (𝓞 K)ˣ :=
  (rayOneElements m).comap (integralUnitsToRayElements m)

/-- Membership in the ray-one unit subgroup is the ray-one property. -/
@[simp] theorem mem_integralRayOneUnits_iff (m : Modulus K) (u : (𝓞 K)ˣ) :
    u ∈ integralRayOneUnits m ↔
      IsRayElementOne m
        ((integralUnitsToRayElements m u : rayElements m) : Kˣ) := by
  unfold integralRayOneUnits
  rw [Subgroup.mem_comap, mem_rayOneElements_iff]
  constructor
  · rintro ⟨hfin, hpos⟩
    exact ⟨(integralUnitsToRayElements m u).property, hfin, hpos⟩
  · rintro ⟨_, hfin, hpos⟩
    exact ⟨hfin, hpos⟩

/-- Inclusion of ray-one units into all integral units (ATLAS `exactSeq_map1`). -/
def integralRayOneUnitsInclusion (m : Modulus K) :
    integralRayOneUnits m →* (𝓞 K)ˣ :=
  (integralRayOneUnits m).subtype

/-- The quotient endpoint map (ATLAS `exactSeq_map2`). -/
def integralUnitsToRayQuotient (m : Modulus K) :
    (𝓞 K)ˣ →* rayElements m ⧸ rayOneElements m :=
  (QuotientGroup.mk' (rayOneElements m)).comp (integralUnitsToRayElements m)

/-- The quotient map evaluated on an integral unit. -/
@[simp] theorem integralUnitsToRayQuotient_apply (m : Modulus K) (u : (𝓞 K)ˣ) :
    integralUnitsToRayQuotient m u =
      QuotientGroup.mk (integralUnitsToRayElements m u) := by
  simp [integralUnitsToRayQuotient]

/-- Transported residue-sign endpoint map. -/
noncomputable def integralUnitsToResidueSign (m : Modulus K) :
    (𝓞 K)ˣ →* ResidueSignTarget m :=
  (rayElementsQuotientEquivResidueSign m).toMonoidHom.comp
    (integralUnitsToRayQuotient m)

/-- The residue-sign map evaluated on an integral unit. -/
@[simp] theorem integralUnitsToResidueSign_apply (m : Modulus K) (u : (𝓞 K)ˣ) :
    integralUnitsToResidueSign m u =
      residueSignMap m (integralUnitsToRayElements m u) := by
  change (rayElementsQuotientEquivResidueSign m)
    (integralUnitsToRayQuotient m u) = _
  rw [integralUnitsToRayQuotient_apply, rayElementsQuotientEquivResidueSign_mk]

/-- Kernel of the quotient endpoint is the ray-one unit subgroup. -/
@[simp] theorem integralUnitsToRayQuotient_ker (m : Modulus K) :
    (integralUnitsToRayQuotient m).ker = integralRayOneUnits m := by
  unfold integralUnitsToRayQuotient integralRayOneUnits
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- Kernel of the residue-sign endpoint is the ray-one unit subgroup. -/
@[simp] theorem integralUnitsToResidueSign_ker (m : Modulus K) :
    (integralUnitsToResidueSign m).ker = integralRayOneUnits m := by
  unfold integralUnitsToResidueSign
  rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _),
    integralUnitsToRayQuotient_ker]
end Modulus
end NumberField
