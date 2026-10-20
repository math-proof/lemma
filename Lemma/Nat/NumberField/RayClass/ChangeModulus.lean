import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.ChangeModulus
open scoped nonZeroDivisors
open NumberField.Modulus


/--
[rayGroupAmbient_le_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
private lemma rayGroupAmbient_le_coprime_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  rayGroupAmbient m ≤ coprimeFractionalIdeals m := by
-- proof
  apply NumberField.Modulus.rayGroupAmbient_le_coprime m

/--
[CongruenceSubgroup.rayGroupAmbient_le_toAmbientSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
private lemma CongruenceSubgroup_rayGroupAmbient_le_toAmbientSubgroup_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {C : CongruenceSubgroup m} :
-- imply
  rayGroupAmbient m ≤ C.toAmbientSubgroup := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroup.rayGroupAmbient_le_toAmbientSubgroup C

/--
[coprimeFractionalIdeals_le_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
private lemma coprimeFractionalIdeals_le_of_dvd_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
-- given
  (h : m2 ∣ m1) :
-- imply
  coprimeFractionalIdeals m1 ≤ coprimeFractionalIdeals m2 := by
-- proof
  apply NumberField.Modulus.coprimeFractionalIdeals_le_of_dvd h

/--
[changeModulus_toAmbientSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
private lemma changeModulus_toAmbientSubgroup_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {C1 : CongruenceSubgroup m1} :
-- imply
  (changeModulus C1 m2).toAmbientSubgroup =
    (C1.toAmbientSubgroup ⊓ coprimeFractionalIdeals m2) ⊔
    rayGroupAmbient m2 := by
-- proof
  apply NumberField.Modulus.changeModulus_toAmbientSubgroup C1

/--
[changeModulus_toAmbientSubgroup_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
private lemma changeModulus_toAmbientSubgroup_of_dvd_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {C1 : CongruenceSubgroup m1}
-- given
  (hdiv : m2 ∣ m1) :
-- imply
  (changeModulus C1 m2).toAmbientSubgroup =
    C1.toAmbientSubgroup ⊔ rayGroupAmbient m2 := by
-- proof
  apply NumberField.Modulus.changeModulus_toAmbientSubgroup_of_dvd C1 hdiv

/--
[changeModulus_isEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
private lemma changeModulus_isEquivalent_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {C1 : CongruenceSubgroup m1}
-- given
  (hdiv : m2 ∣ m1)
  (hcond : coprimeFractionalIdeals m1 ⊓ rayGroupAmbient m2 ≤ C1.toAmbientSubgroup) :
-- imply
  CongruenceSubgroupPair.IsEquivalent
    { modulus := by
-- proof
  apply NumberField.Modulus.changeModulus_isEquivalent C1 hdiv hcond

/--
[exists_equivalent_iff_changeModulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ChangeModulus.lean)
-/
@[path]
private lemma exists_equivalent_iff_changeModulus_eq
  [Field K] [NumberField K]
  {m1 : Modulus K}
  {C1 : CongruenceSubgroup m1}
  {m2 : Modulus K}
-- given
  (hdiv : m2 ∣ m1) :
-- imply
  (∃ C2 : CongruenceSubgroup m2,
    CongruenceSubgroupPair.IsEquivalent
    { modulus := by
-- proof
  apply NumberField.Modulus.exists_equivalent_iff_changeModulus C1 hdiv


-- created on 2026-10-20
