/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryRadialPatchInterpolant
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (mesh : Real) :
    Complex → Complex :=
  finiteRadialGridInterpolant m mesh (fun i j =>
    fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j /
      (Real.sqrt (2 * mesh) : Complex))

end
end StatMech.Universality
