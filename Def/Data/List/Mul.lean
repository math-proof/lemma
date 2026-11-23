module

public import Mathlib.Data.Nat.GCD.Basic
public import Def.Data.Tensor.Defs.Part4

@[expose] public section

namespace Tensor

/-- Left-pad with `1`s to length `n` (PyTorch-style rank alignment). -/
def pad1 (s : List ℕ) (n : ℕ) : List ℕ :=
  List.replicate (n - s.length) 1 ++ s


end Tensor
