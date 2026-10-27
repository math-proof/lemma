import Mathlib.Data.Nat.GCD.Basic
import Def.Data.Holor.Defs.Part4
import Theorem.Data.List.Mul


namespace Tensor

/--
Output shape of `Tensor.mul`.

Right-align the shapes (left-pad `1`s), then take `Nat.lcm` on each axis.
`lcm 0 x = 0`, so a zero-size axis stays zero.
-/
def mul_shape (s s' : List ℕ) : List ℕ :=
  let n := s.length ⊔ s'.length
  (pad1 s n).zipWith Nat.lcm (pad1 s' n)

end Tensor
