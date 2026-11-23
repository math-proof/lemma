/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/


module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
public import Theorem.Nat.Cyclotomic.CubicResidueSymbol
public import Def.MathlibExtTest.NumberTheory.Cyclotomic.CubicResidueSymbol.Part2
@[expose] public section

namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

instance instThreePID :
    IsPrincipalIdealRing
      (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
  IsCyclotomicExtension.Rat.three_pid (K := CyclotomicField 3 ℚ)

end MetaMathlibExtTest
