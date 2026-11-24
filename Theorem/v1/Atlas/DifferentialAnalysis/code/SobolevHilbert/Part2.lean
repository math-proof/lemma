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
public import Instance.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert


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

/-- Underlying-function form of addition on `SobolevSpace n m`. -/
@[simp] lemma sobolevSpace_add_toFun {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) : (u + v).toFun = u.toFun + v.toFun := rfl

/-- Underlying-function form of negation on `SobolevSpace n m`. -/
@[simp] lemma sobolevSpace_neg_toFun {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m) : (-u).toFun = -u.toFun := rfl

/-- The underlying function of the zero element is the zero function. -/
@[simp] lemma sobolevSpace_zero_toFun (n m : ℕ) :
    (0 : SobolevEmbedding.SobolevSpace n m).toFun = 0 := rfl

end SobolevHilbert
end
