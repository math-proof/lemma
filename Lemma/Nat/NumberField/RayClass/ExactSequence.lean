import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.ExactSequence
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[fractionalIdealMk0_mem_coprimeFractionalIdeals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
private lemma fractionalIdealMk0_mem_coprimeFractionalIdeals_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {I : nonZeroDivisors (Ideal (𝓞 K))}
-- given
  (hI : IsCoprime (I : Ideal (𝓞 K)) (m.finitePart : Ideal (𝓞 K))) :
-- imply
  FractionalIdeal.mk0 K I ∈ coprimeFractionalIdeals m := by
-- proof
  apply NumberField.Modulus.fractionalIdealMk0_mem_coprimeFractionalIdeals m I hI

/--
[coprimeIdealClassMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
private lemma coprimeIdealClassMap_surjective_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Surjective (coprimeIdealClassMap m) := by
-- proof
  apply NumberField.Modulus.coprimeIdealClassMap_surjective m

/--
[rayClassToClassGroup_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
private lemma rayClassToClassGroup_surjective_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Surjective (rayClassToClassGroup m) := by
-- proof
  apply NumberField.Modulus.rayClassToClassGroup_surjective m

/--
[rayClass_six_term_exact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
private lemma rayClass_six_term_exact_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Injective (integralRayOneUnitsInclusion m) ∧
    Function.MulExact (integralRayOneUnitsInclusion m)
    (integralUnitsToRayQuotient m) ∧
    Function.MulExact (integralUnitsToRayQuotient m)
    (rayQuotientToRayClassGroup m) ∧
    Function.MulExact (rayQuotientToRayClassGroup m)
    (rayClassToClassGroup m) ∧
    Function.Surjective (rayClassToClassGroup m) := by
-- proof
  apply NumberField.Modulus.rayClass_six_term_exact m

/--
[rayClass_residueSign_six_term_exact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
private lemma rayClass_residueSign_six_term_exact_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Injective (integralRayOneUnitsInclusion m) ∧
    Function.MulExact (integralRayOneUnitsInclusion m)
    (integralUnitsToResidueSign m) ∧
    Function.MulExact (integralUnitsToResidueSign m)
    (residueSignToRayClassGroup m) ∧
    Function.MulExact (residueSignToRayClassGroup m)
    (rayClassToClassGroup m) ∧
    Function.Surjective (rayClassToClassGroup m) := by
-- proof
  apply NumberField.Modulus.rayClass_residueSign_six_term_exact m


-- created on 2026-10-20
