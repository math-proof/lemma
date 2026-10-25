/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
open Finset


namespace StatMech.Universality

noncomputable section

def isingCenteredSum (f : Nat → Real) (center i : Nat) : Real :=
  if center ≤ i then ∑ k ∈ Ico center i, f k
  else -∑ k ∈ Ico i center, f k

end
end StatMech.Universality
