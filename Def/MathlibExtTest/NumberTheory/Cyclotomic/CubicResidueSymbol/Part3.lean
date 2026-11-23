/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/

module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
public import Theorem.Nat.Cyclotomic.CubicResidueSymbol
public import Instance.MathlibExtTest.NumberTheory.Cyclotomic.CubicResidueSymbol.Part3

@[expose] public section

namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

noncomputable def concretePrime :
    NumberField.RingOfIntegers (CyclotomicField 3 ℚ) :=
  Submodule.IsPrincipal.generator concretePrimeIdeal

end MetaMathlibExtTest
