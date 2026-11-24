module
public import Def.NumberTheory.NumberField.RayClass.Character
public import Theorem.Nat.NumberField.RayClass.Character
public import Theorem.NumberTheory.NumberField.RayClass.InducedCharacter


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean -/
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

/-- Natural level-change map on coprime fractional ideals. -/
def coprimeInclusion (h : m1 ∣ m2) :
    coprimeFractionalIdeals m2 →* coprimeFractionalIdeals m1 :=
  Subgroup.inclusion (coprime_le_of_dvd h)

end Modulus
end NumberField
