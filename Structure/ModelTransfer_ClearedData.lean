import Instance.FLTPrelim_Modularity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open WeierstrassCurve

namespace FLT.ModelTransfer


structure ClearedData (C : VariableChange ℚ) where

  N : ℕ

  hN : N ≠ 0

  U : ℤ

  U' : ℤ

  R : ℤ

  S : ℤ

  T : ℤ

  hU : (U : ℚ) = (N : ℚ) * (C.u : ℚ)

  hU' : (U' : ℚ) = (N : ℚ) * ((C.u : ℚ))⁻¹

  hR : (R : ℚ) = (N : ℚ) * C.r

  hS : (S : ℚ) = (N : ℚ) * C.s

  hT : (T : ℚ) = (N : ℚ) * C.t


namespace ClearedData

variable {C : VariableChange ℚ} (D : ClearedData C)


end ClearedData

section IntegerIdentities

variable {V W : WeierstrassCurve ℤ} {C : VariableChange ℚ}


end IntegerIdentities

section Reduction

variable {C : VariableChange ℚ} (D : ClearedData C)
variable {q : ℕ} [Fact q.Prime]


variable (hq : ¬ q ∣ D.N)


end Reduction

end FLT.ModelTransfer
