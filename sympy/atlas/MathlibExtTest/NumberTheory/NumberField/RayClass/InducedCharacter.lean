/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/InducedCharacter.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.InducedCharacter
import Lemma.Nat.NumberField.RayClass.InducedCharacter

@[expose] public noncomputable section

open scoped Classical nonZeroDivisors
open NumberField

namespace N428InducedCharacterTest

variable {K : Type*} [Field K] [NumberField K]
variable {m1 m2 : Modulus K}

example (h : m1 ∣ m2) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Modulus.finiteExponent m1 v ≤ Modulus.finiteExponent m2 v :=
  Modulus.finiteExponent_le_of_dvd h v

example (h : m1 ∣ m2) (x : Kˣ) (hx : Modulus.IsRayElementOne m2 x) :
    Modulus.IsRayElementOne m1 x :=
  Modulus.IsRayElementOne.of_dvd h hx

example (h : m1 ∣ m2) (x : Modulus.coprimeFractionalIdeals m2) :
    Modulus.RayClassGroup.mapOfDvd h (Modulus.rayClassMap m2 x) =
      Modulus.rayClassMap m1 (Modulus.coprimeInclusion h x) :=
  Modulus.RayClassGroup.mapOfDvd_rayClassMap h x

example (h : m1 ∣ m2) :
    (Modulus.trivialCharacter m2).IsInducedBy (Modulus.trivialCharacter m1) h := by
  show (1 : Modulus.RayClassCharacter m2) =
    (1 : Modulus.RayClassCharacter m1).comp (Modulus.RayClassGroup.mapOfDvd h)
  simp

example (chi2 : Modulus.RayClassCharacter m2) (chi1 : Modulus.RayClassCharacter m1)
    (h : m1 ∣ m2) :
    (chi2.IsInducedBy chi1 h ↔ ∀ x : Modulus.coprimeFractionalIdeals m2,
      Modulus.pullback chi2 x =
        Modulus.pullback chi1 (Modulus.coprimeInclusion h x)) :=
  Modulus.RayClassCharacter.isInducedBy_iff chi2 chi1 h

example (chi : Modulus.RayClassCharacter m2) :
    (chi.IsPrimitive ↔ ∀ (m0 : Modulus K) (chi0 : Modulus.RayClassCharacter m0)
      (h : m0 ∣ m2), chi = chi0.comp (Modulus.RayClassGroup.mapOfDvd h) → m0 = m2) :=
  Modulus.RayClassCharacter.isPrimitive_iff chi

end N428InducedCharacterTest
