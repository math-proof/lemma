module

public import Theorem.Matrix.Lift48
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic

public section

set_option autoImplicit false

namespace LanglandsTunnell

open FLT.ExplicitLift Matrix.Lift48

public theorem P16_mul_pw_seven :
    ∀ x ∈ P16, x * pw x 7 = 1 ∧ pw x 7 * x = 1 ∧ pw x 7 ∈ P16 := by
  decide

variable {L : Type} [Field L] [NumberField L]


public theorem mem_sylowH_iff (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (γ : L ≃ₐ[ℚ] L) :
    γ ∈ sylowH e ↔ ∃ M ∈ P16,
      M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Iff.rfl

end LanglandsTunnell
