/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean -/

import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Combinatorics.Enumerative.Partition.Basic
/-!
# The Landau function

The Landau function is the maximum least common multiple of the parts of an
integer partition of `n`.

## References

- [E. Rowland, M. Stipulanti, R. Yassawi, *An elementary proof of Bridy's
  theorem*](https://arxiv.org/abs/2308.10977)
-/


namespace Nat

namespace Partition

/-- The least common multiple of the parts of an integer partition. -/
def partsLCM {n : ℕ} (p : n.Partition) : ℕ :=
  p.parts.lcm

end Partition

/-- The maximum least common multiple of the parts of a partition of `n`. -/
def landauFunction (n : ℕ) : ℕ :=
  Finset.univ.sup (fun p : n.Partition => p.partsLCM)

end Nat
