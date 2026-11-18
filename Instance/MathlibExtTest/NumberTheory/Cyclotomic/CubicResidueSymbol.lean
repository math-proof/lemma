/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/

module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
public import Theorem.Nat.Cyclotomic.CubicResidueSymbol

@[expose] public section

namespace MetaMathlibExtTest

open MetaMathlibExt Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 3)

-- Zero branch: cubicResidueSymbolRaw a 0 = 0

instance : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  @CyclotomicField.isCyclotomicExtension 3 ⟨by decide⟩ ℚ _ ⟨by norm_num⟩

end MetaMathlibExtTest
