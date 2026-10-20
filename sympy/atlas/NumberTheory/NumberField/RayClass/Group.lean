/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Group.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.RayGroup
/-!
# Ray class groups as quotients (N404)

The ray class group of a modulus `m` is the quotient of the group of
fractional ideals coprime to `m` by the ray group.
-/

@[expose] noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Ray class group of a modulus: coprime ideals modulo the ray group. -/
abbrev RayClassGroup (m : Modulus K) :=
  ↥(coprimeFractionalIdeals m) ⧸ rayGroup m

/-- Canonical projection onto the ray class group. -/
def rayClassMap (m : Modulus K) :
    coprimeFractionalIdeals m →* RayClassGroup m :=
  QuotientGroup.mk' (rayGroup m)

theorem rayClassMap_surjective (m : Modulus K) :
    Function.Surjective (rayClassMap (K := K) m) :=
  QuotientGroup.mk'_surjective _

@[simp] theorem rayClassMap_ker (m : Modulus K) :
    MonoidHom.ker (rayClassMap (K := K) m) = rayGroup m :=
  QuotientGroup.ker_mk' _

@[simp] theorem rayClassMap_eq_one_iff (m : Modulus K)
    (x : coprimeFractionalIdeals m) :
    rayClassMap m x = 1 ↔ x ∈ rayGroup m :=
  QuotientGroup.eq_one_iff x

theorem rayClassMap_eq_rayClassMap_iff (m : Modulus K)
    (a b : coprimeFractionalIdeals m) :
    rayClassMap m a = rayClassMap m b ↔ a / b ∈ rayGroup m :=
  by simpa [rayClassMap, RayClassGroup] using
    (QuotientGroup.eq_iff_div_mem (N := rayGroup m) (x := a) (y := b))

end Modulus
end NumberField
