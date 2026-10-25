import Lemma.LanglandsTunnell.Lift48
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false

namespace LanglandsTunnell

open FLT.ExplicitLift LanglandsTunnell.Lift48

private theorem P16_mul_pw_seven :
    ∀ x ∈ P16, x * pw x 7 = 1 ∧ pw x 7 * x = 1 ∧ pw x 7 ∈ P16 := by
  decide

variable {L : Type} [Field L] [NumberField L]

def sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Subgroup (L ≃ₐ[ℚ] L) where
  carrier := {γ | ∃ M ∈ P16,
    M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))}
  one_mem' := ⟨1, one_mem_P16.1, by rw [map_one, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)]⟩
  mul_mem' := by
    rintro a b ⟨M, hM, hMa⟩ ⟨N, hN, hNb⟩
    exact ⟨M * N, P16_mul_closed M hM N hN, by rw [Matrix.map_mul, hMa, hNb, map_mul, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨M, hM, hMa⟩
    refine ⟨pw M 7, (P16_mul_pw_seven M hM).2.2, ?_⟩
    rw [map_inv]
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    rw [← hMa, ← Matrix.map_mul, (P16_mul_pw_seven M hM).1, Matrix.map_one _ (map_zero red) (map_one red)]

theorem mem_sylowH_iff (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (γ : L ≃ₐ[ℚ] L) :
    γ ∈ sylowH e ↔ ∃ M ∈ P16,
      M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Iff.rfl

end LanglandsTunnell
