import sympy.vector.vector
import sympy.functions.elementary.exponential
open Vector

namespace List.Vector

instance [Exp α] : Exp (Vector α n) where
  exp a := a.map Exp.exp
  exp_add x y := by
    ext i
    simp [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply Exp.exp_add


instance [Log α] : Log (Vector α n) where
  log a := a.map Log.log


def softmax [Zero α] [Div α] [Exp α] (x : Vector α n) : Vector α n :=
  let x_exp := exp x
  x_exp / x_exp.sum

end List.Vector
