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
import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part7


noncomputable section

open MeasureTheory

namespace SobolevHilbert

attribute [local instance] sobolevSpace_nacg


/-- Promote a Schwartz function to an element of `SobolevSpace n m`. -/
def schwartzToSobolev (n m : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    SobolevEmbedding.SobolevSpace n m :=
  ⟨⇑φ, φ.smooth m, fun j hj => schwartz_iteratedFDeriv_memLp φ j hj⟩

end SobolevHilbert
end
