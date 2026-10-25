/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part9


namespace StatMech.Universality

def isingLeapfrogBoxReflectX (R : Nat) (p : IsingLeapfrogBox R) :
    IsingLeapfrogBox R :=
  (⟨R - p.1.1, by omega⟩, p.2)

end StatMech.Universality
