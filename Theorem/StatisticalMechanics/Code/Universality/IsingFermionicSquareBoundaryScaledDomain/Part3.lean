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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_medial
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    fkIsingSquareBoundaryPerturbedHolomorphicInterpolant n hn mesh hmesh
        (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) =
      (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a := by
  unfold fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
  rw [finiteLagrangeInterpolant_apply _ _
    (fkIsingSquareWiredPerturbedCarrierPosition_injective n hn mesh hmesh)]
  rfl


theorem fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_differentiable
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    Differentiable Complex
      (fkIsingSquareBoundaryPerturbedHolomorphicInterpolant n hn mesh hmesh) := by
  unfold fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
  exact differentiable_finiteLagrangeInterpolant _ _

end
end StatMech.Universality
