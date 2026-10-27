import Mathlib.Data.Nat.GCD.Basic
import Def.Data.Holor.Defs.Part4
import Theorem.Data.List.Mul.Part3


namespace Tensor

/--
Heterogeneous tensor multiplication `A.mul B`.

Shapes are right-aligned and combined with per-axis `lcm`. Data is the
pointwise product after wrapping each axis (`wrapFlat`).
-/
def mul [Mul α] (A : Tensor α s) (B : Tensor α s') :
    Tensor α (mul_shape s s') :=
  if h : (mul_shape s s').prod = 0 then
    ⟨cast (congrArg (List.Vector α) h.symm) List.Vector.nil⟩
  else
    ⟨List.Vector.ofFn fun i =>
      A.data.get ⟨wrapFlat (pad1 s (s.length ⊔ s'.length)) (mul_shape s s') i.val,
        wrapFlat_lt_src s s' i.val h⟩ *
      B.data.get ⟨wrapFlat (pad1 s' (s.length ⊔ s'.length)) (mul_shape s s') i.val,
        wrapFlat_lt_src' s s' i.val h⟩⟩


end Tensor
