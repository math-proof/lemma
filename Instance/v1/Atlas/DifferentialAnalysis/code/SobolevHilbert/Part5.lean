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
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part6


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


/-- The complex `NormedSpace` structure on `SobolevSpace n m`. -/
instance sobolevSpace_normedSpace' (n m : ℕ) :
    @NormedSpace ℂ (SobolevEmbedding.SobolevSpace n m) _
      (sobolevSpace_nacg n m).toSeminormedAddCommGroup :=
  @NormedSpace.mk ℂ _ _ (sobolevSpace_nacg n m).toSeminormedAddCommGroup
    (sobolevSpace_module' n m) (fun c u => sobolevSpace_norm_smul_le c u)


end SobolevHilbert
end
