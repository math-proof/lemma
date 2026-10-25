/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean -/

import Theorem.NumberTheory.NumberField.RayClass.ResidueSign.Part3
import Lemma.Nat.NumberField.RayClass.ResidueSign
@[expose] noncomputable section

open scoped nonZeroDivisors

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


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Principal-ideal map out of ray elements, landing in ideals coprime to `m`. -/
noncomputable def principalRayIdealMap (m : Modulus K) :
    rayElements m →* coprimeFractionalIdeals m :=
  ((toPrincipalIdeal (𝓞 K) K).domRestrict (rayElements m)).codRestrict
    (coprimeFractionalIdeals m)
    (fun x => (mem_rayElements_iff m _).mp x.property)

end Modulus
end NumberField
