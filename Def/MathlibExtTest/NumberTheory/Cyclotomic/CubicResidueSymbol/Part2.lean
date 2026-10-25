/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/


import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
import Lemma.Nat.Cyclotomic.CubicResidueSymbol
import Instance.MathlibExtTest.NumberTheory.Cyclotomic.CubicResidueSymbol.Part2


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
