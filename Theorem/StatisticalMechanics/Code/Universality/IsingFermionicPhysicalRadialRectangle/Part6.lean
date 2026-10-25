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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareInteriorRadialFiniteRectanglePlacement

variable {n width height : Nat} {hn : 0 < n}


theorem carrier_increment_closed_on
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) :
    IsingRectangleClosedOneFormOn
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (P.horizontalCarrier i j))
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (P.verticalCarrier i j)) width height := by
  simpa [horizontalCarrier, verticalCarrier, horizontalIncrement,
    verticalIncrement,
    FKIsingSquareInteriorRadialRectanglePlacement.primitiveIncrement_carrier]
    using P.increment_closed_on


theorem physicalNormalized_normSq_sum_le
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height)
    (C mesh L : Real)
    (hupper : ∀ i ≤ width, ∀ j ≤ height,
      fkIsingSquareWiredIntegratedPrimitive n hn
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
  apply isingRectangle_physicalNormalized_normSq_sum_le_on
    (fkIsingSquareWiredObservableGrid n hn P.horizontalCarrier)
    (fkIsingSquareWiredObservableGrid n hn P.verticalCarrier)
    C mesh L width height
  · simpa [fkIsingSquareWiredObservableGrid,
      fkIsingSquareWiredPrimitiveIncrement, isingPrimitiveIncrement] using
      P.carrier_increment_closed_on
  · intro i hi j hj
    exact fkIsingSquareWiredIntegratedPrimitive_nonneg n hn
      P.horizontalCarrier P.verticalCarrier i j
  · exact hupper
  · exact hmesh
  · exact hC
  · exact hscale

end FKIsingSquareInteriorRadialFiniteRectanglePlacement
end
end StatMech.Universality
