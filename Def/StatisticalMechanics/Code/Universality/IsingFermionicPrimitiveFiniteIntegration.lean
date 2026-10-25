/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveFiniteIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration


namespace StatMech.Universality

open Finset

noncomputable section

def IsingRectangleClosedOneFormOn
    (horizontal vertical : Nat → Nat → Real)
    (width height : Nat) : Prop :=
  ∀ i < width, ∀ j < height,
    vertical i j + horizontal i (j + 1) =
      horizontal i j + vertical (i + 1) j

end
end StatMech.Universality
