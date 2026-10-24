/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/ExactSequence.lean -/

import Lemma.Nat.NumberField.RayClass.ExactSequence

@[expose] public noncomputable section

open scoped nonZeroDivisors
open NumberField

namespace N406ExactSequenceTest

variable {K : Type*} [Field K] [NumberField K]

-- Bridge: coprime integral ideals land in coprime fractional ideals.
example (m : Modulus K) (I : nonZeroDivisors (Ideal (𝓞 K)))
    (hI : IsCoprime (I : Ideal (𝓞 K))
      (m.finitePart : Ideal (𝓞 K))) :
    FractionalIdeal.mk0 K I ∈ Modulus.coprimeFractionalIdeals m :=
  Modulus.fractionalIdealMk0_mem_coprimeFractionalIdeals m I hI

-- Surjectivity of the coprime ideal-class map.
example (m : Modulus K) (c : ClassGroup (𝓞 K)) :
    ∃ I, Modulus.coprimeIdealClassMap m I = c :=
  Modulus.coprimeIdealClassMap_surjective m c

-- Surjectivity of the ray-class projection.
example (m : Modulus K) (c : ClassGroup (𝓞 K)) :
    ∃ q, Modulus.rayClassToClassGroup m q = c :=
  Modulus.rayClassToClassGroup_surjective m c

-- Raw wrapper projection 1: injectivity at ray-one units.
example (m : Modulus K) :
    Function.Injective (Modulus.integralRayOneUnitsInclusion m) :=
  (Modulus.rayClass_six_term_exact m).1

-- Raw wrapper projection 2: exactness at integral units.
example (m : Modulus K) :
    Function.MulExact (Modulus.integralRayOneUnitsInclusion m)
      (Modulus.integralUnitsToRayQuotient m) :=
  (Modulus.rayClass_six_term_exact m).2.1

-- Raw wrapper projection 3: exactness at the quotient.
example (m : Modulus K) :
    Function.MulExact (Modulus.integralUnitsToRayQuotient m)
      (Modulus.rayQuotientToRayClassGroup m) :=
  (Modulus.rayClass_six_term_exact m).2.2.1

-- Raw wrapper projection 4: exactness at the ray class group.
example (m : Modulus K) :
    Function.MulExact (Modulus.rayQuotientToRayClassGroup m)
      (Modulus.rayClassToClassGroup m) :=
  (Modulus.rayClass_six_term_exact m).2.2.2.1

-- Raw wrapper projection 5: surjectivity of the projection.
example (m : Modulus K) :
    Function.Surjective (Modulus.rayClassToClassGroup m) :=
  (Modulus.rayClass_six_term_exact m).2.2.2.2

-- Residue-sign wrapper projection 1: injectivity at ray-one units.
example (m : Modulus K) :
    Function.Injective (Modulus.integralRayOneUnitsInclusion m) :=
  (Modulus.rayClass_residueSign_six_term_exact m).1

-- Residue-sign wrapper projection 2: exactness at integral units.
example (m : Modulus K) :
    Function.MulExact (Modulus.integralRayOneUnitsInclusion m)
      (Modulus.integralUnitsToResidueSign m) :=
  (Modulus.rayClass_residueSign_six_term_exact m).2.1

-- Residue-sign wrapper projection 3: exactness at the residue-sign target.
example (m : Modulus K) :
    Function.MulExact (Modulus.integralUnitsToResidueSign m)
      (Modulus.residueSignToRayClassGroup m) :=
  (Modulus.rayClass_residueSign_six_term_exact m).2.2.1

-- Residue-sign wrapper projection 4: exactness at the ray class group.
example (m : Modulus K) :
    Function.MulExact (Modulus.residueSignToRayClassGroup m)
      (Modulus.rayClassToClassGroup m) :=
  (Modulus.rayClass_residueSign_six_term_exact m).2.2.2.1

-- Residue-sign wrapper projection 5: surjectivity of the projection.
example (m : Modulus K) :
    Function.Surjective (Modulus.rayClassToClassGroup m) :=
  (Modulus.rayClass_residueSign_six_term_exact m).2.2.2.2

-- Arbitrary class preimage through the coprime-ideal bridge.
example (m : Modulus K) (c : ClassGroup (𝓞 K)) :
    ∃ I : Modulus.coprimeFractionalIdeals m,
      Modulus.coprimeIdealClassMap m I = c := by
  obtain ⟨I, hI⟩ := Modulus.coprimeIdealClassMap_surjective m c
  exact ⟨I, hI⟩

-- Identity boundary: the projection sends `1` to `1`.
example (m : Modulus K) :
    Modulus.rayClassToClassGroup m 1 = 1 :=
  map_one _

end N406ExactSequenceTest
