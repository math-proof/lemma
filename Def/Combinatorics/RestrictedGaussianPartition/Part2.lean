/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

module

public import Mathlib.Algebra.IsPrimePow
public import Instance.Combinatorics.RestrictedGaussianPartition

@[expose] public section

namespace MetaMathlibExt

def ChainHeadValid (q : Nat) (blocks : List Block) (i : Nat) (s : BranchStep) : Prop :=
  1 ≤ s.b ∧ s.b ≤ s.a ∧ s.a + s.b = (blockAt blocks i).d ∧ 1 ≤ s.c ∧
    s.c ≤ q ^ branchBoundExp blocks i - 1 ∧ basicCount q blocks i ≠ 1

end MetaMathlibExt
