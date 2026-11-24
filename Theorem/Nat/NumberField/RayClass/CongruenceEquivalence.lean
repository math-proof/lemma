module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.NumberTheory.NumberField.RayClass.CongruenceEquivalence
open scoped nonZeroDivisors
open NumberField.Modulus
open CongruenceSubgroupPair


public section

namespace NumberField.Modulus.CongruenceSubgroupPair

/--
[isEquivalent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceEquivalence.lean)
-/
@[path]
theorem isEquivalent_iff
  [Field K] [NumberField K]
  {P Q : CongruenceSubgroupPair K} :
-- imply
  IsEquivalent P Q ↔
    coprimeFractionalIdeals P.modulus ⊓ Q.subgroup.toAmbientSubgroup =
    coprimeFractionalIdeals Q.modulus ⊓ P.subgroup.toAmbientSubgroup :=
-- proof
  Iff.rfl

end NumberField.Modulus.CongruenceSubgroupPair

namespace NumberField.Modulus.CongruenceSubgroupPair

/--
[IsEquivalent.refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceEquivalence.lean)
-/
@[path]
theorem IsEquivalent.refl
  [Field K] [NumberField K]
  {P : CongruenceSubgroupPair K} :
-- imply
  IsEquivalent P P :=
-- proof
  rfl

end NumberField.Modulus.CongruenceSubgroupPair

namespace NumberField.Modulus.CongruenceSubgroupPair

/--
[IsEquivalent.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceEquivalence.lean)
-/
@[path]
theorem IsEquivalent.symm
  [Field K] [NumberField K]
  {P Q : CongruenceSubgroupPair K} :
-- imply
  IsEquivalent P Q → IsEquivalent Q P :=
-- proof
  Eq.symm

end NumberField.Modulus.CongruenceSubgroupPair


-- created on 2026-10-20
-- updated on 2026-10-26
