/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean -/

import Def.NumberTheory.NumberField.RayClass.Character
import Lemma.Nat.NumberField.RayClass.Character
import Theorem.NumberTheory.NumberField.RayClass.InducedCharacter.Part3
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

/-- A character at `m2` induced by one at `m1` via level change. -/
def RayClassCharacter.IsInducedBy (chi2 : RayClassCharacter m2)
    (chi1 : RayClassCharacter m1) (h : m1 ∣ m2) : Prop :=
  chi2 = chi1.comp (RayClassGroup.mapOfDvd h)

/-- A character is primitive if induced only from the same modulus. -/
def RayClassCharacter.IsPrimitive (chi : RayClassCharacter m2) : Prop :=
  ∀ (m0 : Modulus K) (chi0 : RayClassCharacter m0) (h : m0 ∣ m2),
    chi.IsInducedBy chi0 h → m0 = m2

end Modulus
end NumberField
