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
import Instance.v1.Atlas.DifferentialAnalysis.code.CompactSobolevEmbedding
open MeasureTheory Filter Topology
open scoped ZeroAtInfty


noncomputable section

namespace SchwartzWeightedSobolev

/-- Bundle of a function lying in every weighted Sobolev space, with a
consistent family of weighted Sobolev witnesses. -/
structure MemAllWeightedSobolev (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  mem_weighted (k : ℕ) : WeightedSobolevSpace n k
  consistent (k : ℕ) :
    ∀ x, toFun x = WeightedSobolevSpace.toFun (mem_weighted k) x

end SchwartzWeightedSobolev
end
