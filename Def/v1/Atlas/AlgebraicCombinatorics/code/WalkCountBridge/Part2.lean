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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge


noncomputable section

open scoped Classical

open WalkCountFormula NormalOrderCoeff Finset

namespace WalkCountBridge

def liftU_Q : (YoungDiagram →₀ ℚ) →ₗ[ℚ] (YoungDiagram →₀ ℚ) :=
  Finsupp.lsum ℚ fun μ => LinearMap.id.smulRight (toQ (YoungDiagram.raisingOp μ))

def liftD_Q : (YoungDiagram →₀ ℚ) →ₗ[ℚ] (YoungDiagram →₀ ℚ) :=
  Finsupp.lsum ℚ fun μ => LinearMap.id.smulRight (toQ (YoungDiagram.loweringOp μ))

def emptyBasis_Q : YoungDiagram →₀ ℚ := Finsupp.single ⊥ 1

end WalkCountBridge
end
