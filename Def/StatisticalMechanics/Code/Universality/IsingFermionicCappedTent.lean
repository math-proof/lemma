/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicProductGreenBarrier


namespace StatMech.Universality

noncomputable section

def isingNatCappedTent (source i : Nat) : Real :=
  (Nat.min i source : Nat)


noncomputable def isingNatCappedRobinTent
    (coefficient : Real) (source i : Nat) : Real :=
  isingNatCappedTent source i + 1 / coefficient


def isingNatReverseCappedTent (top source i : Nat) : Real :=
  isingNatCappedTent (top - source) (top - i)

end
end StatMech.Universality
