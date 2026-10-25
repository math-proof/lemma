/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

import Mathlib.Algebra.IsPrimePow
import Def.Combinatorics.RestrictedGaussianPartition.Part3


namespace MetaMathlibExt

instance decChainAdjValid (ch : List BranchStep) :
    Decidable (ChainAdjValid ch) := by
  unfold ChainAdjValid
  exact inferInstance

end MetaMathlibExt
