/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceEquivalence.lean -/

import Def.NumberTheory.NumberField.RayClass.CongruenceSubgroup
import Lemma.Nat.NumberField.RayClass.CongruenceSubgroup
/-!
# Congruence subgroup pair equivalence (N420 Definition 22.3)

Pairs of a modulus with a congruence subgroup for it, and the
equivalence relation comparing two pairs inside the common ambient
group of all nonzero fractional ideals. Transitivity is not claimed
here; it needs arithmetic approximation (N421).
-/


noncomputable section

open scoped nonZeroDivisors

namespace NumberField.Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- A modulus together with a congruence subgroup for it. -/
structure CongruenceSubgroupPair (K : Type*) [Field K] [NumberField K] where
  /-- The modulus of the pair. -/
  modulus : Modulus K
  /-- The congruence subgroup for `modulus`. -/
  subgroup : CongruenceSubgroup modulus

end NumberField.Modulus
end
