/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean -/

import Def.NumberTheory.NumberField.RayClass.Group
import Lemma.Nat.NumberField.RayClass.Group
/-!
# Congruence subgroups (N419 Definition 22.1)
A congruence subgroup is a subgroup of the coprime ideals
containing the ray group. Its image in the ray class group,
ambient version, smallest/largest examples follow.
-/


noncomputable section

open scoped nonZeroDivisors

namespace NumberField.Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Congruence subgroup for `m`: subgroup of coprime ideals
containing the ray group. -/
@[ext] structure CongruenceSubgroup (m : Modulus K) where
  /-- Underlying subgroup of the coprime ideals. -/
  toSubgroup : Subgroup (coprimeFractionalIdeals m)
  /-- The ray group is contained in the subgroup. -/
  rayGroup_le : rayGroup m ≤ toSubgroup

end NumberField.Modulus
end
