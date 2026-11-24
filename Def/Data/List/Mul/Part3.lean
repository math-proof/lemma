module
public import Mathlib.Data.Nat.GCD.Basic
public import Def.Data.Tensor.Defs.Part4
public import Theorem.Data.List.Mul.Part2


public section

namespace Tensor

/--
Row-major wrap of a flat index `i` of `out` back into shape `s`.

On each axis: `(coord_out % out_axis) % s_axis`.
Requires `s.length = out.length`.
-/
def wrapFlat : List ℕ → List ℕ → ℕ → ℕ
  | n :: s, k :: tout, i =>
    (i / tout.prod % k % n) * s.prod + wrapFlat s tout i
  | _, _, _ => 0


end Tensor
