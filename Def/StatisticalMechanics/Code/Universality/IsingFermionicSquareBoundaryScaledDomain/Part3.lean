/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8
import Theorem.StatisticalMechanics.Code.Universality.FiniteHolomorphicInterpolation
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    Complex → Complex :=
  finiteLagrangeInterpolant
    (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh)
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable


end
end StatMech.Universality
