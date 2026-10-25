/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.NormalOrderCoeff
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps


noncomputable section

open scoped Classical

open WalkCountFormula NormalOrderCoeff Finset

namespace WalkCountBridge

def toQ : (YoungDiagram →₀ ℤ) → (YoungDiagram →₀ ℚ) :=
  Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero

end WalkCountBridge
end
