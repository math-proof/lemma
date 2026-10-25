/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean -/

import Mathlib.Algebra.IsPrimePow
import Instance.Combinatorics.RestrictedGaussianPartition.Part4


namespace MetaMathlibExt

/-- A Gaussian partition `G` is a restricted Gaussian partition for prime power `q`
and positive `n` when its dimensions arise from valid descending blocks, each
realized independently with at most one nonempty simultaneous-split branch, every
intermediate global list stays nonincreasing, and the target equals the realized
final dimensions exactly. -/
def IsRestrictedGaussianPartition (q n : Nat) (G : GaussianPartition) : Prop :=
  IsPrimePow q ∧ 0 < n ∧
    ∃ (blocks : List Block) (chains : List (List BranchStep)),
      chains.length = blocks.length ∧
      BlocksStructValid blocks n ∧
      (∀ i, i < blocks.length → BranchValid q blocks i (chainAt chains i)) ∧
      ∃ (finals : List (List Nat)),
        allFinalDims q blocks chains = some finals ∧
        (basicGlobalDims q blocks).Pairwise (fun a b : Nat => a ≥ b) ∧
        finals.flatten.Pairwise (fun a b : Nat => a ≥ b) ∧
        (∀ i, i < blocks.length →
          ∀ k, k < (chainAt chains i).length →
            (stageGlobalDims q blocks chains finals i k).all
              (fun g => decide (g.Pairwise (fun a b : Nat => a ≥ b))) = true) ∧
        G.dims = finals.flatten

end MetaMathlibExt
