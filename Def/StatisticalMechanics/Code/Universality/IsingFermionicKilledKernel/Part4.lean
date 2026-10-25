/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel


namespace StatMech.Universality

open Finset

noncomputable section

def isingLeapfrogPlaneSW (p : IsingLeapfrogPlane) : IsingLeapfrogPlane :=
  (p.1 - 1, p.2 - 1)

def isingLeapfrogPlaneSE (p : IsingLeapfrogPlane) : IsingLeapfrogPlane :=
  (p.1 + 1, p.2 - 1)

def isingLeapfrogPlaneNW (p : IsingLeapfrogPlane) : IsingLeapfrogPlane :=
  (p.1 - 1, p.2 + 1)

def isingLeapfrogPlaneNE (p : IsingLeapfrogPlane) : IsingLeapfrogPlane :=
  (p.1 + 1, p.2 + 1)


noncomputable def isingLeapfrogFreeKernel :
    Nat → IsingLeapfrogPlane → IsingLeapfrogPlane → Real
  | 0, p, q => if p = q then 1 else 0
  | t + 1, p, q =>
      (isingLeapfrogFreeKernel t (isingLeapfrogPlaneSW p) q +
        isingLeapfrogFreeKernel t (isingLeapfrogPlaneSE p) q +
        isingLeapfrogFreeKernel t (isingLeapfrogPlaneNW p) q +
        isingLeapfrogFreeKernel t (isingLeapfrogPlaneNE p) q) / 4

end
end StatMech.Universality
