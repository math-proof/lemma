import stdlib.List.Vector
import sympy.functions.elementary.exponential
open Algebra


instance [Exp α] : Exp (List.Vector α n) where
  exp a := a.map Exp.exp
  exp_add x y := by
    ext i
    simp [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply Exp.exp_add


instance [Log α] : Log (List.Vector α n) where
  log a := a.map Log.log
