import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.Character
open scoped nonZeroDivisors
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[trivialCharacter_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma trivialCharacter_apply
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : RayClassGroup m} :
-- imply
  trivialCharacter m x = 1 :=
-- proof
  rfl

end NumberField.Modulus

namespace NumberField.Modulus

/--
[RayClassCharacter_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma RayClassCharacter_apply_one
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m} :
-- imply
  chi 1 = 1 :=
-- proof
  map_one chi

end NumberField.Modulus

namespace NumberField.Modulus

/--
[RayClassCharacter_apply_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma RayClassCharacter_apply_mul
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {a b : RayClassGroup m} :
-- imply
  chi (a * b) = chi a * chi b :=
-- proof
  map_mul chi a b

end NumberField.Modulus

namespace NumberField.Modulus

/--
[pullback_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma pullback_apply
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {x : coprimeFractionalIdeals m} :
-- imply
  pullback chi x = chi (rayClassMap m x) :=
-- proof
  rfl

end NumberField.Modulus

namespace NumberField.Modulus

/--
[pullback_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma pullback_one
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m} :
-- imply
  pullback chi 1 = 1 :=
-- proof
  map_one _

end NumberField.Modulus

namespace NumberField.Modulus

/--
[pullback_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma pullback_mul
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {a b : coprimeFractionalIdeals m} :
-- imply
  pullback chi (a * b) = pullback chi a * pullback chi b :=
-- proof
  map_mul _ _ _

end NumberField.Modulus

namespace NumberField.Modulus

/--
[pullback_eq_one_of_mem_rayGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma pullback_eq_one_of_mem_rayGroup
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {x : coprimeFractionalIdeals m}
-- given
  (h : x ∈ rayGroup m) :
-- imply
  pullback chi x = 1 := by
-- proof
  rw [pullback_apply, (rayClassMap_eq_one_iff m x).mpr h, map_one]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[evalComplex_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma evalComplex_one
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m} :
-- imply
  evalComplex chi 1 = 1 := by
-- proof
  simp only [evalComplex, map_one]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[evalComplex_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma evalComplex_mul
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {a b : RayClassGroup m} :
-- imply
  evalComplex chi (a * b) = evalComplex chi a * evalComplex chi b := by
-- proof
  simp only [evalComplex, map_mul]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[evalComplex_rayGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma evalComplex_rayGroup
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {x : coprimeFractionalIdeals m}
-- given
  (h : x ∈ rayGroup m) :
-- imply
  evalComplex chi (rayClassMap m x) = 1 := by
-- proof
  rw [(rayClassMap_eq_one_iff m x).mpr h, evalComplex_one]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[extendByZero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma extendByZero_of_mem
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
  simp [extendByZero, h]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[extendByZero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Character.lean)
-/
@[path]
lemma extendByZero_of_not_mem
  [Field K] [NumberField K]
  {m : Modulus K}
  {chi : RayClassCharacter m}
  {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
-- given
  (h : I ∉ coprimeFractionalIdeals m) :
-- imply
  extendByZero chi I = 0 := by
-- proof
  simp [extendByZero, h]

end NumberField.Modulus


-- created on 2026-10-20
-- updated on 2026-10-23
