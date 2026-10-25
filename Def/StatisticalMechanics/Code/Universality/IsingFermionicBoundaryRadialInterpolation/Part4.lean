/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def complexBilinearCell
    (a00 a10 a01 a11 : Complex) (x y : Real) : Complex :=
  ((1 - x) * (1 - y) : Real) * a00 +
    (x * (1 - y) : Real) * a10 +
    ((1 - x) * y : Real) * a01 +
    (x * y : Real) * a11


end
end StatMech.Universality
