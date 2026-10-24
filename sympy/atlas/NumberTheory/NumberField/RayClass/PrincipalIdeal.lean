/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.ResidueSign
import Lemma.Nat.NumberField.RayClass.ResidueSign
/-!
# Principal-ideal bridge for ray elements (N406 E2)

Supporting stage for ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the principal-ideal map out of ray elements, equality of principal ideals
modulo integral units, and equality of the ray group with the image of
ray-one elements.

Source: `Atlas/NumberTheoryI/code/RayClassFields.lean`
(`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`), N406.

Source-to-API map:
- ATLAS principal-ideal membership for ray elements, lines 1054--1091,
  to `principalRayIdealMap` and `principalRayIdealMap_apply`;
- ATLAS congruent principal ideals lie in the ray group, lines 1093--1108,
  to the reverse inclusion of `rayGroup_eq_map_rayOneElements`;
- ATLAS integral-unit extraction from equality of principal ideals,
  lines 1160--1204, to `toPrincipalIdeal_eq_iff_exists_integralUnit_mul`;
- ATLAS valuation/subtype reconstruction, lines 1206--1247, is obsolete
  (current `rayElements` is definitionally the comap of `toPrincipalIdeal`)
  and is not ported;
- ATLAS ray-group containment in the principal image, lines 1249--1282,
  to the forward inclusion of `rayGroup_eq_map_rayOneElements`
  (strengthened here to an equality).

This is E2 supporting work: it does not include the quotient lift at
source lines 1110--1118, any exactness declarations at line 1284 onward,
or the full six-term exact sequence / full N406.
-/

@[expose] noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Principal-ideal map out of ray elements, landing in ideals coprime to `m`. -/
noncomputable def principalRayIdealMap (m : Modulus K) :
    rayElements m →* coprimeFractionalIdeals m :=
  ((toPrincipalIdeal (𝓞 K) K).domRestrict (rayElements m)).codRestrict
    (coprimeFractionalIdeals m)
    (fun x => (mem_rayElements_iff m _).mp x.property)

/-- Pointwise evaluation of the principal-ideal map on ray elements. -/
@[simp] theorem principalRayIdealMap_apply (m : Modulus K) (x : rayElements m) :
    (principalRayIdealMap m x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
  rfl

/-- The ray group is exactly the image of ray-one elements. -/
theorem rayGroup_eq_map_rayOneElements (m : Modulus K) :
    rayGroup m = (rayOneElements m).map (principalRayIdealMap m) := by
  apply le_antisymm
  · apply rayGroup_closure_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxmem : (⟨x, hx.1⟩ : rayElements m) ∈ rayOneElements m :=
      (mem_rayOneElements_iff m _).mpr ⟨hx.2.1, hx.2.2⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hxmem, ?_⟩
    apply Subtype.ext
    exact principalRayIdealMap_apply m _
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := Subgroup.mem_map.mp hz
    have hIsOne : IsRayElementOne m (x : Kˣ) := by
      obtain ⟨hcongr, hpos⟩ := (mem_rayOneElements_iff m x).mp hx
      exact ⟨x.property, hcongr, hpos⟩
    have hmem := mem_rayGroup_of_isRayElementOne m (x : Kˣ) hIsOne
    rw [← hzx]
    convert hmem using 1
    apply Subtype.ext
    exact (principalRayIdealMap_apply m x).symm

end Modulus
end NumberField
