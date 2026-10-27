import Mathlib.Data.Nat.GCD.Basic
import Def.Data.Holor.Defs.Part4


namespace Tensor

/-- Left-pad with `1`s to length `n` (PyTorch-style rank alignment). -/
def pad1 (s : List ℕ) (n : ℕ) : List ℕ :=
  List.replicate (n - s.length) 1 ++ s


end Tensor
