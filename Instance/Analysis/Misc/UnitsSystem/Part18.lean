import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem.Part20
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

noncomputable instance Scalar.instPosSMulStrictMono (d:Dimensions) : PosSMulStrictMono ℝ (Scalar d) where
  smul_lt_smul_of_pos_left {_a} ha {_b₁ _b₂} hb := by
    simp only [val_lt, val_smul, smul_eq_mul] at *; exact mul_lt_mul_of_pos_left hb ha

noncomputable instance Scalar.instSMulPosStrictMono (d:Dimensions) : SMulPosStrictMono ℝ (Scalar d) where
  smul_lt_smul_of_pos_right {_b} hb {_a₁ _a₂} ha := by
    simp only [val_lt, val_smul, smul_eq_mul] at *; exact mul_lt_mul_of_pos_right ha hb

noncomputable instance Scalar.instIsStrictOrderedModule (d:Dimensions) : IsStrictOrderedModule ℝ (Scalar d) where

end UnitsSystem
