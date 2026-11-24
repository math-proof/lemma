module
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.WeightedSobolevSchwartz
public import Def.v1.Atlas.DifferentialAnalysis.code.WeightedSobolevSchwartz
public import Def.v1.Atlas.DifferentialAnalysis.code.CompactSobolevEmbedding
open MeasureTheory Filter Topology
open scoped ZeroAtInfty


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CompactSobolevEmbedding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace SchwartzWeightedSobolev

/-- Coercion that lets an element of `WeightedSobolevSpace n k` be applied as
a function `EuclideanSpace ℝ (Fin n) → ℂ`. -/
instance {n k : ℕ} : CoeFun (WeightedSobolevSpace n k)
    (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨WeightedSobolevSpace.toFun⟩

end SchwartzWeightedSobolev
end
