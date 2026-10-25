/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/SparseBallCard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part5
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
open Finset Real


noncomputable section

namespace SparseVarshamovGilbert

/-- Support of a binary vector: the finset of coordinates where `x i = true`. -/
def boolSupport {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i = true)

/-- Modify `x` by clearing the bits indexed by `J` and setting those indexed
by `K`, leaving the rest unchanged. Used to step between nearby sparse vectors. -/
def flipVec {d : ℕ} (x : Fin d → Bool) (J K : Finset (Fin d)) : Fin d → Bool :=
  fun i => if i ∈ J then false else if i ∈ K then true else x i

end SparseVarshamovGilbert
end
