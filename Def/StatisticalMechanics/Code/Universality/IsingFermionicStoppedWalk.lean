/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk


namespace StatMech.Universality

open Finset

noncomputable section

def isingLeapfrogBoxBoundary (R : Nat) (p : IsingLeapfrogBox R) : Prop :=
  p.1.1 = 0 ∨ p.1.1 + 1 = R + 1 ∨
    p.2.1 = 0 ∨ p.2.1 + 1 = R + 1

end
end StatMech.Universality
