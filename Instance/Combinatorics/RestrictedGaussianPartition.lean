/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

module

public import Mathlib.Algebra.IsPrimePow
public import Def.Combinatorics.RestrictedGaussianPartition

@[expose] public section

namespace MetaMathlibExt

instance decBlocksStructValid (blocks : List Block) (n : Nat) :
    Decidable (BlocksStructValid blocks n) := by
  unfold BlocksStructValid
  exact inferInstance

end MetaMathlibExt
