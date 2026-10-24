/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/OrthonormalBases.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

open scoped InnerProductSpace

namespace OrthonormalBases

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def IsOrthonormalSequence (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (φ : ℕ → E) : Prop :=
  Orthonormal 𝕜 φ

end OrthonormalBases

end

namespace HilbertSpace

class IsHilbertSpace (𝕜 : Type*) (E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] : Prop

end HilbertSpace
