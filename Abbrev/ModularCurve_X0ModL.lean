import Mathlib
import Def.ModularCurve_JqCoeff
import Def.ModularCurve_LaurentCoeff
import Class.AlgebraicCurve_DivisorClassGroup
import Lemma.ModularCurve.CoeffSemilinearAut
import Lemma.ModularCurve.QAdicPlaceMod

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve

namespace ModularCurve

section CoeffMapSupply

variable {R S : Type*} [CommRing R] [CommRing S]

end CoeffMapSupply

section JExpansion

variable (R : Type*) [CommRing R]

end JExpansion

section QExpandAlg

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]


end QExpandAlg

section FunctionField

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]


end FunctionField

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

abbrev JZeroC : Type _ := Pic0 K (modularFunctionFieldFullC K N)

end Jacobian

end ModularCurve

end
