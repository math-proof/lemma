import Mathlib
import Class.AlgebraicCurve_DivisorClassGroup
import Lemma.ModularCurve.JqCoeff
import Def.ModularCurve_WeightDivisor

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]


theorem weightDivisor_apply (m : ℕ)
    (h : ∃ D : Divisor K ↥(modularFunctionFieldC K N), ∀ w, D w = weightFloor K N m w)
    (w : Place K ↥(modularFunctionFieldC K N)) :
    weightDivisor K N m w = weightFloor K N m w := by
  classical
  rw [weightDivisor, dif_pos h]
  exact h.choose_spec w

end ModularCurve

end
