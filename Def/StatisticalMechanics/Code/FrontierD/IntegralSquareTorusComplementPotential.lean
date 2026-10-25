/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryOpenPathPotential


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def sub (C D : IntegralSquareTorusCycle L) : IntegralSquareTorusCycle L where
  horizontal p := C.horizontal p - D.horizontal p
  vertical p := C.vertical p - D.vertical p
  divergence_zero p := by
    have hC := C.divergence_zero p
    have hD := D.divergence_zero p
    linear_combination hC - hD

end IntegralSquareTorusCycle
end
end StatMech.FrontierD
