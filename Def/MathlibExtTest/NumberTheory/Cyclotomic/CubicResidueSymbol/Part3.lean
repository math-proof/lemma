/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/


import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
import Lemma.Nat.Cyclotomic.CubicResidueSymbol
import Instance.MathlibExtTest.NumberTheory.Cyclotomic.CubicResidueSymbol.Part3


namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

noncomputable def concretePrime :
    NumberField.RingOfIntegers (CyclotomicField 3 ℚ) :=
  Submodule.IsPrincipal.generator concretePrimeIdeal

end MetaMathlibExtTest
