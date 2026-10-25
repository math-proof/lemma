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
import Def.v1.Atlas.DifferentialAnalysis.code.CompactSobolevEmbedding
open MeasureTheory Filter Topology
open scoped ZeroAtInfty


noncomputable section

namespace SchwartzWeightedSobolev

/-- Coercion that lets an element of `WeightedSobolevSpace n k` be applied as
a function `EuclideanSpace ℝ (Fin n) → ℂ`. -/
instance {n k : ℕ} : CoeFun (WeightedSobolevSpace n k)
    (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨WeightedSobolevSpace.toFun⟩

end SchwartzWeightedSobolev
end
