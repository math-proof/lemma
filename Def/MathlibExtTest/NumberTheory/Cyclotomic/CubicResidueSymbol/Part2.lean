/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/

module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
public import Theorem.Nat.Cyclotomic.CubicResidueSymbol
public import Instance.MathlibExtTest.NumberTheory.Cyclotomic.CubicResidueSymbol.Part2

@[expose] public section

namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

noncomputable def concretePrimeIdealSubtype :
    ↥(Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) :=
  Classical.choice inferInstance

noncomputable def concretePrimeIdeal :
    Ideal (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
  concretePrimeIdealSubtype.val

end MetaMathlibExtTest
