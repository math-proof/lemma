/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/


module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
public import Theorem.Nat.Cyclotomic.CubicResidueSymbol
public import Def.MathlibExtTest.NumberTheory.Cyclotomic.CubicResidueSymbol
@[expose] public section

namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance span_two_isPrime :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime Int.prime_two

end MetaMathlibExtTest
