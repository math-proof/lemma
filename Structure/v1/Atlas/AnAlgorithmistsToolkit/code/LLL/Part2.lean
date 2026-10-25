/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.LLL.Part2


noncomputable section

open InnerProductSpace Finset

namespace LLL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IsReducedBasis (b : Fin n → E) : Prop where
  size_reduced : IsSizeReduced b
  lovász_original : SatisfiesLovászOriginal b

end LLL
end
