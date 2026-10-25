/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Group.lean -/

import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
import Lemma.Nat.NumberField.RayClass.RayGroup
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Ray class groups as quotients (N404)

The ray class group of a modulus `m` is the quotient of the group of
fractional ideals coprime to `m` by the ray group.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Ray class group of a modulus: coprime ideals modulo the ray group. -/
abbrev RayClassGroup (m : Modulus K) :=
  ↥(coprimeFractionalIdeals m) ⧸ rayGroup m

end Modulus
end NumberField
