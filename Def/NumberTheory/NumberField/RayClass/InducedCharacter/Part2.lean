/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean -/

import Def.NumberTheory.NumberField.RayClass.Character
import Lemma.Nat.NumberField.RayClass.Character
import Theorem.NumberTheory.NumberField.RayClass.InducedCharacter.Part2
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

/-- Level-change map on ray class groups. -/
def RayClassGroup.mapOfDvd (h : m1 ∣ m2) : RayClassGroup m2 →* RayClassGroup m1 :=
  QuotientGroup.map (rayGroup m2) (rayGroup m1) (coprimeInclusion h) (rayGroup_le_comap_of_dvd h)

end Modulus
end NumberField
