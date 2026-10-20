import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.Character
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[trivialCharacter_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma trivialCharacter_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : RayClassGroup m} :
-- imply
  trivialCharacter m x = 1 := by
-- proof
  apply NumberField.Modulus.trivialCharacter_apply m x

/--
[RayClassCharacter_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma RayClassCharacter_apply_one_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m} :
-- imply
  chi 1 = 1 := by
-- proof
  apply NumberField.Modulus.RayClassCharacter_apply_one chi

/--
[RayClassCharacter_apply_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma RayClassCharacter_apply_mul_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {a b : RayClassGroup m} :
-- imply
  chi (a * b) = chi a * chi b := by
-- proof
  apply NumberField.Modulus.RayClassCharacter_apply_mul chi a b

/--
[pullback_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma pullback_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {x : coprimeFractionalIdeals m} :
-- imply
  pullback chi x = chi (rayClassMap m x) := by
-- proof
  apply NumberField.Modulus.pullback_apply chi x

/--
[pullback_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma pullback_one_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m} :
-- imply
  pullback chi 1 = 1 := by
-- proof
  apply NumberField.Modulus.pullback_one chi

/--
[pullback_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma pullback_mul_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {a b : coprimeFractionalIdeals m} :
-- imply
  pullback chi (a * b) = pullback chi a * pullback chi b := by
-- proof
  apply NumberField.Modulus.pullback_mul chi a b

/--
[pullback_eq_one_of_mem_rayGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma pullback_eq_one_of_mem_rayGroup_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {x : coprimeFractionalIdeals m}
-- given
  (h : x ∈ rayGroup m) :
-- imply
  pullback chi x = 1 := by
-- proof
  apply NumberField.Modulus.pullback_eq_one_of_mem_rayGroup chi x h

/--
[evalComplex_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma evalComplex_one_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m} :
-- imply
  evalComplex chi 1 = 1 := by
-- proof
  apply NumberField.Modulus.evalComplex_one chi

/--
[evalComplex_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma evalComplex_mul_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {a b : RayClassGroup m} :
-- imply
  evalComplex chi (a * b) = evalComplex chi a * evalComplex chi b := by
-- proof
  apply NumberField.Modulus.evalComplex_mul chi a b

/--
[evalComplex_rayGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma evalComplex_rayGroup_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {x : coprimeFractionalIdeals m}
-- given
  (h : x ∈ rayGroup m) :
-- imply
  evalComplex chi (rayClassMap m x) = 1 := by
-- proof
  apply NumberField.Modulus.evalComplex_rayGroup chi x h

/--
[extendByZero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma extendByZero_of_mem_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
-- given
  (h : I ∈ coprimeFractionalIdeals m) :
-- imply
  extendByZero chi I =
    Circle.coeHom (chi (rayClassMap m ⟨I, h⟩)) := by
-- proof
  apply NumberField.Modulus.extendByZero_of_mem chi I h

/--
[extendByZero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
private lemma extendByZero_of_not_mem_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
-- given
  (h : I ∉ coprimeFractionalIdeals m) :
-- imply
  extendByZero chi I = 0 := by
-- proof
  apply NumberField.Modulus.extendByZero_of_not_mem chi I h


-- created on 2026-10-20
