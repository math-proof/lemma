/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareInteriorRadialRectanglePlacement

variable {n : Nat} {hn : 0 < n}

theorem carrier_increment_closed
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    IsingRectangleClosedOneForm
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (P.horizontalCarrier i j))
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (P.verticalCarrier i j)) := by
  simpa [horizontalCarrier, verticalCarrier, horizontalIncrement,
    verticalIncrement, primitiveIncrement_carrier] using P.increment_closed


theorem physicalNormalized_normSq_sum_le
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn)
    (C mesh L : Real) (width height : Nat)
    (hupper : ∀ i j, fkIsingSquareWiredIntegratedPrimitive n hn
      P.horizontalCarrier P.verticalCarrier i j ≤ C)
    (hmesh : 0 < mesh) (hC : 0 ≤ C)
    (hscale : mesh * (height + width) ≤ L) :
    mesh ^ 2 *
        ((∑ j ∈ Finset.range height, ∑ i ∈ Finset.range width,
            Complex.normSq
              (fkIsingSquareWiredObservableGrid n hn P.horizontalCarrier i j /
                (Real.sqrt (2 * mesh) : Complex))) +
          (∑ i ∈ Finset.range width, ∑ j ∈ Finset.range height,
            Complex.normSq
              (fkIsingSquareWiredObservableGrid n hn P.verticalCarrier i j /
                (Real.sqrt (2 * mesh) : Complex)))) ≤
      L * C / 2 := by
  exact fkIsingSquareWired_physicalNormalized_normSq_sum_le n hn
    P.horizontalCarrier P.verticalCarrier P.carrier_increment_closed
    C mesh L width height hupper hmesh hC hscale

end FKIsingSquareInteriorRadialRectanglePlacement
end
end StatMech.Universality
