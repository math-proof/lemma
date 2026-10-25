/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/Character.lean -/

import Def.NumberTheory.NumberField.RayClass.Character
import Lemma.Nat.NumberField.RayClass.Character
@[expose] public noncomputable section

open scoped Classical nonZeroDivisors
open NumberField


namespace N427RayClassCharacterTest

variable {K : Type*} [Field K] [NumberField K]

example (m : Modulus K) : Modulus.trivialCharacter m 1 = 1 := rfl

example (m : Modulus K) (x : Modulus.RayClassGroup m) :
    Modulus.trivialCharacter m x = 1 :=
  Modulus.trivialCharacter_apply m x

example (m : Modulus K) (chi : Modulus.RayClassCharacter m) :
    chi 1 = 1 :=
  map_one chi

example (m : Modulus K) (chi : Modulus.RayClassCharacter m)
    (a b : Modulus.RayClassGroup m) :
    chi (a * b) = chi a * chi b :=
  map_mul chi a b

example (m : Modulus K) (chi : Modulus.RayClassCharacter m)
    (x : Modulus.coprimeFractionalIdeals m) :
    Modulus.pullback chi x = chi (Modulus.rayClassMap m x) :=
  rfl

example (m : Modulus K) (chi : Modulus.RayClassCharacter m) :
    Modulus.pullback chi 1 = 1 :=
  map_one _

example (m : Modulus K) (chi : Modulus.RayClassCharacter m)
    (x : Modulus.coprimeFractionalIdeals m)
    (h : x ∈ Modulus.rayGroup m) :
    Modulus.pullback chi x = 1 :=
  Modulus.pullback_eq_one_of_mem_rayGroup chi x h

example (m : Modulus K) (chi : Modulus.RayClassCharacter m)
    (x : Modulus.coprimeFractionalIdeals m)
    (h : x ∈ Modulus.rayGroup m) :
    Modulus.evalComplex chi (Modulus.rayClassMap m x) = 1 :=
  Modulus.evalComplex_rayGroup chi x h

example (m : Modulus K) (chi : Modulus.RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : I ∈ Modulus.coprimeFractionalIdeals m) :
    Modulus.extendByZero chi I =
      Circle.coeHom (chi (Modulus.rayClassMap m ⟨I, h⟩)) :=
  Modulus.extendByZero_of_mem chi I h

example (m : Modulus K) (chi : Modulus.RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : I ∉ Modulus.coprimeFractionalIdeals m) :
    Modulus.extendByZero chi I = 0 :=
  Modulus.extendByZero_of_not_mem chi I h

end N427RayClassCharacterTest
