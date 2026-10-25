/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HilbertSpace
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Class.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part5


noncomputable section

open MeasureTheory

namespace SobolevHilbert

attribute [local instance] sobolevSpace_nacg


/-- The `ℂ`-module structure on `SobolevSpace n m`. -/
instance sobolevSpace_module' (n m : ℕ) :
    Module ℂ (SobolevEmbedding.SobolevSpace n m) :=
  { smul := (· • ·)
    mul_smul := fun a b u =>
      SobolevEmbedding.SobolevSpace.ext' (mul_smul a b u.toFun)
    one_smul := fun u =>
      SobolevEmbedding.SobolevSpace.ext' (one_smul ℂ u.toFun)
    smul_zero := fun a =>
      SobolevEmbedding.SobolevSpace.ext' (smul_zero a)
    smul_add := fun a u v =>
      SobolevEmbedding.SobolevSpace.ext' (smul_add a u.toFun v.toFun)
    add_smul := fun a b u =>
      SobolevEmbedding.SobolevSpace.ext' (add_smul a b u.toFun)
    zero_smul := fun u =>
      SobolevEmbedding.SobolevSpace.ext' (zero_smul ℂ u.toFun) }


end SobolevHilbert
end
