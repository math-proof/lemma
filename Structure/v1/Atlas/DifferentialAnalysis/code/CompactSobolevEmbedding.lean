/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CompactSobolevEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WeightedSobolevSchwartz
import Def.v1.Atlas.DifferentialAnalysis.code.WeightedSobolevSchwartz
open MeasureTheory Filter Topology
open scoped ZeroAtInfty


noncomputable section

namespace SchwartzWeightedSobolev

/-- The `k`-th weighted Sobolev space on `ℝⁿ`: a structure recording an
underlying Sobolev representative, used to model functions `f` such that
`⟨x⟩^k · f ∈ H^k`. -/
structure WeightedSobolevSpace (n : ℕ) (k : ℕ) where
  witness : SobolevEmbedding.SobolevSpace n k

end SchwartzWeightedSobolev
end
