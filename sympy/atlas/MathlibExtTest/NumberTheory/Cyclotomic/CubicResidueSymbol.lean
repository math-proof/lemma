/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/


import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import sympy.atlas.NumberTheory.Cyclotomic.CubicResidueSymbol
import Lemma.Nat.Cyclotomic.CubicResidueSymbol


namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

-- Zero branch: cubicResidueSymbolRaw a 0 = 0

instance : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  @CyclotomicField.isCyclotomicExtension 3 ⟨by decide⟩ ℚ _ ⟨by norm_num⟩

-- Concrete third cyclotomic instantiation

noncomputable def concreteZeta : CyclotomicField 3 ℚ :=
  IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)
instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance span_two_isPrime :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime Int.prime_two

noncomputable def concretePrimeIdealSubtype :
    ↥(Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) :=
  Classical.choice inferInstance

noncomputable def concretePrimeIdeal :
    Ideal (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
  concretePrimeIdealSubtype.val

instance instThreePID :
    IsPrincipalIdealRing
      (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
  IsCyclotomicExtension.Rat.three_pid (K := CyclotomicField 3 ℚ)

noncomputable def concretePrime :
    NumberField.RingOfIntegers (CyclotomicField 3 ℚ) :=
  Submodule.IsPrincipal.generator concretePrimeIdeal
