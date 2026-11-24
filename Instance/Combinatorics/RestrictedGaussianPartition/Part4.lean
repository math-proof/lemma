module
public import Mathlib.Algebra.IsPrimePow
public import Def.Combinatorics.RestrictedGaussianPartition.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/
namespace MetaMathlibExt

instance decBranchValid (q : Nat) (blocks : List Block) (i : Nat)
    (ch : List BranchStep) : Decidable (BranchValid q blocks i ch) := by
  cases ch with
  | nil => exact isTrue True.intro
  | cons s rest =>
    exact inferInstanceAs
      (Decidable (ChainHeadValid q blocks i s ∧ ChainAdjValid (s :: rest)))

end MetaMathlibExt
