/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean -/

import Def.NumberTheory.NumberField.RayClass.Character
import Lemma.Nat.NumberField.RayClass.Character
import Def.NumberTheory.NumberField.RayClass.InducedCharacter.Part2
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Induced ray class characters (N428 Definition 22.12)

If `m1 ∣ m2`, a ray class character at `m2` is induced by one at `m1`
when their values agree on ideals coprime to `m2` under level change.
A character is primitive when it is induced only from the same modulus.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K] {m1 m2 : Modulus K}

/-- `mapOfDvd` on canonical representatives. -/
@[simp] theorem RayClassGroup.mapOfDvd_rayClassMap (h : m1 ∣ m2)
    (x : coprimeFractionalIdeals m2) :
    mapOfDvd h (rayClassMap m2 x) = rayClassMap m1 (coprimeInclusion h x) := by
  simp only [mapOfDvd, rayClassMap, QuotientGroup.mk'_apply, QuotientGroup.map_mk]

end Modulus
end NumberField
