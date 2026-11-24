module
public import Mathlib
public import Theorem.Ideal.NormClass
public import Def.NumberField_RayCharacterData
set_option autoImplicit false
set_option linter.unusedSectionVars false


public section

noncomputable section

namespace NumberField.NormResidueChar

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply
open LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K] (m : ℕ) [NeZero m]

abbrev fm : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)}

section Cyclo

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]

end Cyclo

end NumberField.NormResidueChar

end
