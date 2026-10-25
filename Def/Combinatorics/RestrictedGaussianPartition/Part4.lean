/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

import Mathlib.Algebra.IsPrimePow
import Instance.Combinatorics.RestrictedGaussianPartition.Part3


namespace MetaMathlibExt

/-- Branch validity: the root-specific head condition applies to the FIRST step
only; every later step is constrained by the adjacent-chain condition over
consecutive pairs. An empty chain means no branch and is valid. -/
def BranchValid (q : Nat) (blocks : List Block) (i : Nat)
    (ch : List BranchStep) : Prop :=
  match ch with
  | [] => True
  | s :: _ => ChainHeadValid q blocks i s ∧ ChainAdjValid ch

end MetaMathlibExt
