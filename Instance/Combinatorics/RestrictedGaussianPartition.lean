/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

import Mathlib.Algebra.IsPrimePow
import Def.Combinatorics.RestrictedGaussianPartition


namespace MetaMathlibExt

instance decBlocksStructValid (blocks : List Block) (n : Nat) :
    Decidable (BlocksStructValid blocks n) := by
  unfold BlocksStructValid
  exact inferInstance

end MetaMathlibExt
