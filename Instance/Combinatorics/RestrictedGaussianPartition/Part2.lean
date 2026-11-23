/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

module

public import Mathlib.Algebra.IsPrimePow
public import Def.Combinatorics.RestrictedGaussianPartition.Part2
@[expose] public section

namespace MetaMathlibExt

instance decChainHeadValid (q : Nat) (blocks : List Block) (i : Nat)
    (s : BranchStep) : Decidable (ChainHeadValid q blocks i s) := by
  unfold ChainHeadValid
  exact inferInstance

end MetaMathlibExt
