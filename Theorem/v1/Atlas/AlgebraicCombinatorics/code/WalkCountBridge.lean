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
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge


noncomputable section

open scoped Classical

open WalkCountFormula NormalOrderCoeff Finset

namespace WalkCountBridge

@[simp] theorem toQ_apply (f : YoungDiagram →₀ ℤ) (a : YoungDiagram) :
    (toQ f) a = ↑(f a) := by
  show Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero f a = ↑(f a)
  rw [Finsupp.mapRange_apply]

@[simp] theorem toQ_single (a : YoungDiagram) (c : ℤ) :
    toQ (Finsupp.single a c) = Finsupp.single a (↑c : ℚ) := by
  show Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero (Finsupp.single a c) = _
  rw [Finsupp.mapRange_single]

end WalkCountBridge
end
