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
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part3


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
