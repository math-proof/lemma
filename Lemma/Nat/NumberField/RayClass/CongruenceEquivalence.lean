import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.CongruenceEquivalence
open scoped nonZeroDivisors
open NumberField.Modulus
open CongruenceSubgroupPair


/--
[isEquivalent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceEquivalence.lean)
-/
@[path]
private lemma isEquivalent_iff_eq
  [Field K] [NumberField K]
  {P Q : CongruenceSubgroupPair K} :
-- imply
  IsEquivalent P Q ↔
    coprimeFractionalIdeals P.modulus ⊓ Q.subgroup.toAmbientSubgroup =
    coprimeFractionalIdeals Q.modulus ⊓ P.subgroup.toAmbientSubgroup := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroupPair.isEquivalent_iff P Q

/--
[IsEquivalent.refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceEquivalence.lean)
-/
@[path]
private lemma IsEquivalent_refl_eq
  [Field K] [NumberField K]
  {P : CongruenceSubgroupPair K} :
-- imply
  IsEquivalent P P := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroupPair.IsEquivalent.refl P

/--
[IsEquivalent.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceEquivalence.lean)
-/
@[path]
private lemma IsEquivalent_symm_eq
  [Field K] [NumberField K]
  {P Q : CongruenceSubgroupPair K} :
-- imply
  IsEquivalent P Q → IsEquivalent Q P := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroupPair.IsEquivalent.symm


-- created on 2026-10-20
