import Mathlib.Data.Nat.GCD.Basic
import Def.Data.Holor.Defs.Part4
import Def.Data.List.Mul.Part4


namespace Tensor

theorem get_mul [Mul α] (A : Tensor α s) (B : Tensor α s')
    (h : (mul_shape s s').prod ≠ 0)
    (i : Fin (mul_shape s s').prod) :
    (A.mul B).data.get i =
      A.data.get ⟨wrapFlat (pad1 s (s.length ⊔ s'.length)) (mul_shape s s') i.val,
        wrapFlat_lt_src s s' i.val h⟩ *
      B.data.get ⟨wrapFlat (pad1 s' (s.length ⊔ s'.length)) (mul_shape s s') i.val,
        wrapFlat_lt_src' s s' i.val h⟩ := by
  unfold mul
  rw [dite_eq_right h]
  exact List.Vector.get_ofFn _ _

end Tensor
