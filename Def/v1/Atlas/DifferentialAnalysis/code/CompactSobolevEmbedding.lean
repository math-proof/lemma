module
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.WeightedSobolevSchwartz
public import Def.v1.Atlas.DifferentialAnalysis.code.WeightedSobolevSchwartz
public import Structure.v1.Atlas.DifferentialAnalysis.code.CompactSobolevEmbedding
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

/-- The underlying function of a `WeightedSobolevSpace n k` element: divide
the Sobolev witness by `⟨x⟩^k` so that the witness's `Hᵏ` regularity
translates into pointwise `⟨x⟩^k`-decay of the original function. -/
def WeightedSobolevSpace.toFun {n k : ℕ} (u : WeightedSobolevSpace n k)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (↑(TestFunctions.japaneseBracket n x ^ k))⁻¹ * u.witness.toFun x

end SchwartzWeightedSobolev
end
