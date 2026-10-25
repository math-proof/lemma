/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration
open Finset


namespace StatMech.Universality

noncomputable section

def isingCenteredPrimitive
    (horizontal vertical : Nat → Nat → Real)
    (center i j : Nat) : Real :=
  isingCenteredSum (fun k ↦ vertical center k) center j +
    isingCenteredSum (fun k ↦ horizontal k j) center i

end
end StatMech.Universality
