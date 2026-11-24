module
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.HilbertSpace
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
public import Class.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
public import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Instance.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open MeasureTheory

namespace SobolevHilbert

/-- The Sobolev `H^m` norm of `u`: the `ℓ^2` sum of the `L^2` norms of all iterated derivatives up to order `m`. -/
def sobolevNorm {n m : ℕ} (u : SobolevEmbedding.SobolevSpace n m) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (m + 1),
    (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2)

end SobolevHilbert
end
