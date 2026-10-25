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
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge.Part2


noncomputable section

open scoped Classical

open WalkCountFormula NormalOrderCoeff Finset

namespace WalkCountBridge

@[simp] theorem liftU_Q_single (a : YoungDiagram) (c : ℚ) :
    liftU_Q (Finsupp.single a c) = c • toQ (YoungDiagram.raisingOp a) := by simp [liftU_Q]

@[simp] theorem liftD_Q_single (a : YoungDiagram) (c : ℚ) :
    liftD_Q (Finsupp.single a c) = c • toQ (YoungDiagram.loweringOp a) := by simp [liftD_Q]

end WalkCountBridge
end
