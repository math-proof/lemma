/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean -/

import Def.NumberTheory.NumberField.RayClass.Group
import Lemma.Nat.NumberField.RayClass.Group
import Mathlib.Analysis.Complex.Circle
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Ray class characters (N427 Definition 22.10)

A ray class character of a modulus `m` is a homomorphism from the
ray class group to the unit circle. We provide the trivial character,
the pullback to coprime fractional ideals, complex-valued evaluation,
and the extension by zero to all fractional ideals.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

variable {m : Modulus K}

/-- A ray class character: homomorphism from the ray class group to `Circle`. -/
abbrev RayClassCharacter (m : Modulus K) := RayClassGroup m →* Circle

end Modulus
end NumberField
