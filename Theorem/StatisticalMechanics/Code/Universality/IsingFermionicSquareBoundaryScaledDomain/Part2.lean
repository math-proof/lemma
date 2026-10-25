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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareBoundaryPerturbedRawInterpolant_medial
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    fkIsingSquareBoundaryPerturbedRawInterpolant n hn mesh hmesh
        (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) =
      (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a := by
  rw [fkIsingSquareBoundaryPerturbedRawInterpolant, dif_pos ⟨a, rfl⟩]
  have hchosen := Classical.choose_spec
    (show ∃ b : FKIsingSquareWiredCarrier n,
      fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh b =
        fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a from
      ⟨a, rfl⟩)
  have heq : Classical.choose
        (show ∃ b : FKIsingSquareWiredCarrier n,
          fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh b =
            fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a from
          ⟨a, rfl⟩) = a :=
    fkIsingSquareWiredPerturbedCarrierPosition_injective
      n hn mesh hmesh hchosen
  rw [heq]
  rfl


end
end StatMech.Universality
