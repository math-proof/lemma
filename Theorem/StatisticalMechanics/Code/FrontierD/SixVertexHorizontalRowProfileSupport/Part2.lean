/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem actualDeficitTokenHall_rowProfile_iff_capacity
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalActualDeficitTokenHall T
        sourceLeft sourceRight targetLeft targetRight
        (sixVertexHorizontalActualRowProfileSupport T
          sourceLeft sourceRight targetLeft targetRight) ↔
      SixVertexHorizontalRowProfileResidualCapacity T
        sourceLeft sourceRight targetLeft targetRight := by
  classical
  unfold SixVertexHorizontalActualDeficitTokenHall
    sixVertexHorizontalActualRowProfileSupport
    SixVertexHorizontalRowProfileResidualCapacity
  constructor
  · intro hHall grade
    let f := fun source : SixVertexHorizontalActualDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight =>
      sixVertexHorizontalActualDeficitRowProfile source
    let g := fun target : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight =>
      sixVertexHorizontalActualSurplusRowProfile target
    apply (Fintype.hall_equalFiber_iff_card_fibers f g).mp
    intro S
    simpa [f, g] using hHall grade S
  · intro hcapacity grade
    let f := fun source : SixVertexHorizontalActualDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight =>
      sixVertexHorizontalActualDeficitRowProfile source
    let g := fun target : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight =>
      sixVertexHorizontalActualSurplusRowProfile target
    have hHall :=
      (Fintype.hall_equalFiber_iff_card_fibers f g).mpr (hcapacity grade)
    intro S
    simpa [f, g] using hHall S


theorem configurationBigradeFibers_of_rowProfileResidualHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hHall : SixVertexHorizontalActualDeficitTokenHall T
      sourceLeft sourceRight targetLeft targetRight
      (sixVertexHorizontalActualRowProfileSupport T
        sourceLeft sourceRight targetLeft targetRight)) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight :=
  configurationBigradeFibers_of_actualDeficitTokenHall T
    sourceLeft sourceRight targetLeft targetRight _ hHall


theorem configurationBigradeFibers_of_rowProfileResidualCapacity
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hcapacity : SixVertexHorizontalRowProfileResidualCapacity T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  apply configurationBigradeFibers_of_rowProfileResidualHall T
  exact (actualDeficitTokenHall_rowProfile_iff_capacity T
    sourceLeft sourceRight targetLeft targetRight).mpr hcapacity

end
end StatMech.FrontierD
