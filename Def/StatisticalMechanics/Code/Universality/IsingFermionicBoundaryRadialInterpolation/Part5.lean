/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def finiteRadialGridInterpolant
    (m : Nat) (mesh : Real) (value : Fin m → Fin m → Complex)
    (z : Complex) : Complex :=
  ∑ i : Fin m, ∑ j : Fin m,
    ((isingLinearTent ((isingRadialGridCoordinate mesh z).1 - (i.1 : Real)) *
      isingLinearTent ((isingRadialGridCoordinate mesh z).2 - (j.1 : Real)) : Real) :
        Complex) * value i j


end
end StatMech.Universality
