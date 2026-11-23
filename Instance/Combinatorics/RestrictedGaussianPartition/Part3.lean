/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

module

public import Mathlib.Algebra.IsPrimePow
public import Def.Combinatorics.RestrictedGaussianPartition.Part3
@[expose] public section

namespace MetaMathlibExt

instance decChainAdjValid (ch : List BranchStep) :
    Decidable (ChainAdjValid ch) := by
  unfold ChainAdjValid
  exact inferInstance

end MetaMathlibExt
