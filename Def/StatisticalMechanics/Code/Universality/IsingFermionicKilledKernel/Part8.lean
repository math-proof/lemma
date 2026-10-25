/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part7


namespace StatMech.Universality

open Finset

noncomputable section

def isingLeapfrogBoxToPlane {R : Nat}
    (p : IsingLeapfrogBox R) : IsingLeapfrogPlane :=
  ((p.1.1 : Int), (p.2.1 : Int))

end
end StatMech.Universality
