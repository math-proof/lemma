/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/


import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
import Lemma.Nat.Cyclotomic.CubicResidueSymbol
import Instance.MathlibExtTest.NumberTheory.Cyclotomic.CubicResidueSymbol


namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

-- Concrete third cyclotomic instantiation

noncomputable def concreteZeta : CyclotomicField 3 ℚ :=
  IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)

end MetaMathlibExtTest
