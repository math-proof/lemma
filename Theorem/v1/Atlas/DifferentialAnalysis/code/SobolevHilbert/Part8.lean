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
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part3


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

attribute [local instance] sobolevSpace_nacg


/-- The underlying function of `schwartzToSobolev n m φ` is `⇑φ`. -/
@[simp] lemma schwartzToSobolev_toFun (n m : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    (schwartzToSobolev n m φ).toFun = ⇑φ := rfl

end SobolevHilbert
end
